#!/usr/bin/env python3
"""Local helper for Video_Projects_Local.html.

Forwards AI requests from the page to OpenAI (frames) and Seedance / ModelArk
(video), because browsers may block direct calls to these APIs (CORS).
Listens only on 127.0.0.1 (put Cloudflare Tunnel in front of it on a server,
see deploy/). No dependencies beyond the Python standard library.

    python3 ai_server.py            # then press «Проверить соединение» in the page

Keys: a `.env` file next to this script (see .env.example) or the environment
(OPENAI_API_KEY, ARK_API_KEY). A key from the server wins over one typed in
the page; the page hides key fields the server already has.

ChatGPT via Codex: with the Codex CLI logged in with a ChatGPT account
(`codex login`), the page can send OpenAI work here with `X-OpenAI-Via: codex`.
Photo analysis and scene planning run through `codex exec`, frames through
Codex's built-in image tool. These calls take minutes, so they run as jobs:
the request answers 202 {"job": id} and the page polls /api/codex/jobs/<id>.
"""
import base64
import email.parser
import email.policy
import glob
import http.server
import json
import os
import re
import shutil
import ssl
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import webbrowser

ROOT = os.path.dirname(os.path.abspath(__file__))


def load_dotenv(path):
    """KEY=VALUE lines; values already set in the environment win."""
    loaded = []
    try:
        with open(path, encoding="utf-8-sig") as f:
            lines = f.read().splitlines()
    except OSError:
        return loaded
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[7:].lstrip()
        key, sep, value = line.partition("=")
        key, value = key.strip(), value.strip()
        if not sep or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            continue
        if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
            value = value[1:-1]
        else:
            value = value.split(" #", 1)[0].rstrip()
        if value and not os.environ.get(key):
            os.environ[key] = value
            loaded.append(key)
    return loaded


ENV_FILE = os.environ.get("AI_ENV_FILE") or os.path.join(ROOT, ".env")
ENV_LOADED = load_dotenv(ENV_FILE)

PORT = int(os.environ.get("AI_SERVER_PORT", "8787"))
HOST = os.environ.get("AI_SERVER_HOST", "127.0.0.1")
PAGE = "Video_Projects_Local.html"
OPENAI = "https://api.openai.com/v1"
ARK_HOSTS = (".bytepluses.com", ".volces.com", ".byteplus.com", ".volccdn.com")
MEDIA_HOSTS = ARK_HOSTS + (".openai.com", ".oaiusercontent.com", ".blob.core.windows.net")
# On a server behind Cloudflare: AI_ALLOWED_ORIGINS=https://video.example.com
EXTRA_ORIGINS = {o.strip().rstrip("/") for o in os.environ.get("AI_ALLOWED_ORIGINS", "").split(",") if o.strip()}
ALLOWED_ORIGINS = {"null", f"http://127.0.0.1:{PORT}", f"http://localhost:{PORT}"} | EXTRA_ORIGINS
TIMEOUT = 600
MAX_BODY = 200 * 1024 * 1024


def env_key(name):
    return (os.environ.get(name) or "").strip()


def ssl_context():
    try:
        import certifi  # type: ignore
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return ssl.create_default_context()


CTX = ssl_context()


def host_allowed(url, suffixes):
    p = urllib.parse.urlsplit(url)
    host = (p.hostname or "").lower()
    return p.scheme == "https" and any(host.endswith(s) for s in suffixes)


# ---------------------------------------------------------------- Codex ----

CODEX_TIMEOUT = int(os.environ.get("CODEX_TIMEOUT", "600"))
CODEX_EFFORT = os.environ.get("CODEX_EFFORT", "low")
CODEX_MODEL = os.environ.get("CODEX_MODEL", "").strip()
CODEX_SLOTS = threading.BoundedSemaphore(max(1, int(os.environ.get("CODEX_PARALLEL", "2"))))
CODEX_HOME = os.environ.get("CODEX_HOME") or os.path.expanduser("~/.codex")
IMAGE_EXT = (".png", ".jpg", ".jpeg", ".webp")


def find_codex():
    explicit = os.environ.get("CODEX_BIN", "").strip()
    if explicit:
        return explicit if os.path.isfile(explicit) else None
    found = shutil.which("codex")
    if found:
        return found
    # Finder-launched .command files often miss Homebrew / npm paths.
    home = os.path.expanduser("~")
    candidates = ["/opt/homebrew/bin/codex", "/usr/local/bin/codex", home + "/.local/bin/codex",
                  home + "/.npm-global/bin/codex", home + "/.bun/bin/codex", home + "/.volta/bin/codex"]
    candidates += sorted(glob.glob(home + "/.nvm/versions/node/*/bin/codex"), reverse=True)
    for c in candidates:
        if os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    return None


def codex_env(binary):
    env = {k: v for k, v in os.environ.items() if k not in ("OPENAI_API_KEY", "ARK_API_KEY")}
    extra = [os.path.dirname(binary), "/opt/homebrew/bin", "/usr/local/bin"]
    env["PATH"] = os.pathsep.join(extra + [env.get("PATH", "")])
    return env


_codex_state = {"t": 0.0, "value": {"available": False, "loggedIn": False, "chatgpt": False, "message": "ещё не проверен"}}
_codex_lock = threading.Lock()


def refresh_codex_status():
    binary = find_codex()
    if not binary:
        value = {"available": False, "loggedIn": False, "chatgpt": False,
                 "message": "Codex не найден. Установи: npm i -g @openai/codex (или brew install codex)."}
    else:
        try:
            r = subprocess.run([binary, "login", "status"], capture_output=True, text=True, timeout=30,
                               stdin=subprocess.DEVNULL, env=codex_env(binary))
            out = (r.stdout + "\n" + r.stderr).strip()
            logged = r.returncode == 0 and "not logged" not in out.lower()
            chatgpt = logged and "chatgpt" in out.lower()
            msg = ("вход через ChatGPT" if chatgpt else
                   "вход по API-ключу, а не через ChatGPT — выполни codex login" if logged else
                   "не выполнен вход — выполни в Терминале: codex login")
            value = {"available": True, "loggedIn": logged, "chatgpt": chatgpt, "message": msg}
        except Exception as e:
            value = {"available": True, "loggedIn": False, "chatgpt": False, "message": f"не отвечает: {e}"}
    with _codex_lock:
        _codex_state.update(t=time.time(), value=value)
    return value


def codex_status():
    with _codex_lock:
        stale = time.time() - _codex_state["t"] > 30
        value = dict(_codex_state["value"])
    if stale:
        with _codex_lock:
            _codex_state["t"] = time.time()  # one refresh at a time
        threading.Thread(target=refresh_codex_status, daemon=True).start()
    return value


class CodexError(Exception):
    pass


def run_codex(args, prompt, workdir, log_path):
    binary = find_codex()
    if not binary:
        raise CodexError("Codex не найден на этом компьютере. Установи его: npm i -g @openai/codex, затем codex login.")
    cmd = [binary, "exec", "--skip-git-repo-check", "-C", workdir]
    if CODEX_MODEL:
        cmd += ["-m", CODEX_MODEL]
    if CODEX_EFFORT:
        cmd += ["-c", f'model_reasoning_effort="{CODEX_EFFORT}"']
    cmd += args + ["--", prompt]
    with CODEX_SLOTS, open(log_path, "wb") as log:
        try:
            r = subprocess.run(cmd, cwd=workdir, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                               timeout=CODEX_TIMEOUT, env=codex_env(binary))
        except subprocess.TimeoutExpired:
            raise CodexError(f"Codex не уложился в {CODEX_TIMEOUT} с.")
    if r.returncode != 0:
        raise CodexError("Codex завершился с ошибкой: " + log_tail(log_path))


def log_tail(path, n=600):
    try:
        with open(path, "rb") as f:
            text = f.read().decode("utf-8", "replace")
    except OSError:
        return "нет журнала"
    lines = [l for l in text.splitlines() if l.strip()]
    msgs = []
    for l in lines:  # --json logs: pull out error messages
        try:
            ev = json.loads(l)
        except ValueError:
            continue
        if not isinstance(ev, dict) or ev.get("type") not in ("error", "turn.failed"):
            continue
        err = ev.get("error")
        m = ev.get("message") or (err.get("message") if isinstance(err, dict) else err)
        if m:
            msgs.append(str(m))
    tail = " | ".join(msgs) if msgs else " ".join(lines[-6:])
    hint = ""
    if re.search(r"usage limit|rate limit|429", tail, re.I):
        hint = " Похоже, исчерпан лимит подписки ChatGPT — подожди или переключись на API-ключ."
    elif re.search(r"login|auth|401", tail, re.I):
        hint = " Выполни в Терминале: codex login."
    return tail[-n:] + hint


def save_data_url(url, workdir, n):
    m = re.match(r"data:image/(png|jpe?g|webp|gif);base64,(.+)$", url or "", re.S)
    if not m:
        return None
    ext = {"jpeg": "jpg"}.get(m.group(1), m.group(1))
    path = os.path.join(workdir, f"image-{n}.{ext}")
    with open(path, "wb") as f:
        f.write(base64.b64decode(m.group(2)))
    return path


def codex_chat(payload):
    """OpenAI chat.completions request (text + images) -> one `codex exec` run."""
    work = tempfile.mkdtemp(prefix="codex-chat-")
    try:
        images, parts = [], []
        for msg in payload.get("messages") or []:
            content, texts = msg.get("content"), []
            if isinstance(content, str):
                texts.append(content)
            elif isinstance(content, list):
                for p in content:
                    if not isinstance(p, dict):
                        continue
                    if p.get("type") == "text":
                        texts.append(str(p.get("text", "")))
                    elif p.get("type") == "image_url":
                        path = save_data_url((p.get("image_url") or {}).get("url", ""), work, len(images) + 1)
                        if path:
                            images.append(path)
                            texts.append(f"[изображение {len(images)}]")
            label = {"system": "ИНСТРУКЦИЯ", "user": "ЗАПРОС", "assistant": "ОТВЕТ"}.get(msg.get("role"), "ЗАПРОС")
            parts.append(label + ":\n" + "\n".join(texts))
        prompt = ("Работай как модель API: не запускай команды, не читай и не создавай файлы. "
                  + (f"К сообщению приложено изображений: {len(images)}, по порядку упоминания. " if images else "")
                  + "\n\n" + "\n\n".join(parts)
                  + "\n\nОтветь только JSON-объектом, без пояснений и без ```.")
        answer = os.path.join(work, "answer.txt")
        args = ["-s", "read-only", "-o", answer]
        for path in images:
            args += ["-i", path]
        run_codex(args, prompt, work, os.path.join(work, "codex.log"))
        try:
            with open(answer, encoding="utf-8") as f:
                text = f.read().strip()
        except OSError:
            text = ""
        if not text:
            raise CodexError("Codex вернул пустой ответ: " + log_tail(os.path.join(work, "codex.log")))
        return {"object": "chat.completion",
                "choices": [{"index": 0, "finish_reason": "stop", "message": {"role": "assistant", "content": text}}]}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def parse_multipart(ctype, body):
    head = b"Content-Type: " + ctype.encode("latin-1") + b"\r\nMIME-Version: 1.0\r\n\r\n"
    msg = email.parser.BytesParser(policy=email.policy.HTTP).parsebytes(head + body)
    fields, files = {}, []
    for part in msg.iter_parts():
        name = part.get_param("name", header="content-disposition")
        data = part.get_payload(decode=True) or b""
        if part.get_filename():
            files.append((part.get_filename(), data))
        elif name:
            fields[name] = data.decode("utf-8", "replace")
    return fields, files


def image_kind(data):
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if data[:3] == b"\xff\xd8\xff":
        return "jpg"
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "webp"
    return None


def codex_image(fields, refs):
    """OpenAI images.generations / images.edits -> Codex's built-in image tool."""
    work = tempfile.mkdtemp(prefix="codex-img-")
    try:
        names = []
        for i, (_, data) in enumerate(refs, 1):
            kind = image_kind(data)
            if not kind:
                continue
            path = os.path.join(work, f"reference-{i}.{kind}")
            with open(path, "wb") as f:
                f.write(data)
            names.append(path)
        size = fields.get("size") or "1024x1536"
        try:
            w, h = (int(x) for x in size.split("x"))
            shape = "vertical" if h > w else "horizontal" if w > h else "square"
        except ValueError:
            shape = "as described"
        prompt = ("Use your built-in image generation tool ($imagegen) exactly once to create one image. "
                  "Do not write scripts and do not draw the image with code. "
                  + (f"Base it on the {len(names)} attached reference image(s): pass num_last_images_to_include:{len(names)} "
                     "in the image tool call so they reach the tool; the product must look exactly like in the references. "
                     if names else "")
                  + f"Image size: {size} ({shape}). "
                  "Save the generated image as out.png in the current working directory, then reply only with the file name."
                  "\n\nImage description:\n" + (fields.get("prompt") or ""))
        args = ["--json", "-s", "workspace-write"]
        for path in names:
            args += ["-i", path]
        log = os.path.join(work, "codex.log")
        started = time.time()
        error = None
        try:
            run_codex(args, prompt, work, log)
        except CodexError as e:  # the picture may exist even if the turn ended badly
            error = e
        found = find_generated(work, log, started, set(names))
        if not found:
            raise error or CodexError("Codex не создал картинку: " + log_tail(log))
        with open(found, "rb") as f:
            data = f.read()
        return {"created": int(time.time()), "data": [{"b64_json": base64.b64encode(data).decode()}]}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def find_generated(work, log, started, exclude):
    def newest(paths):
        ok = [p for p in paths if p not in exclude and p.lower().endswith(IMAGE_EXT)
              and os.path.getsize(p) > 1000 and os.path.getmtime(p) >= started - 1]
        ok = [p for p in ok if image_kind(open(p, "rb").read(12))]
        return max(ok, key=os.path.getmtime) if ok else None

    hit = newest(glob.glob(os.path.join(work, "**", "*"), recursive=True))
    if hit:
        return hit
    thread = None
    try:
        with open(log, encoding="utf-8", errors="replace") as f:
            for line in f:
                m = re.search(r'"thread_id"\s*:\s*"([^"]+)"', line)
                if m:
                    thread = m.group(1)
                    break
    except OSError:
        pass
    if thread:
        return newest(glob.glob(os.path.join(CODEX_HOME, "generated_images", thread, "**", "*"), recursive=True))
    return None


JOBS = {}
JOBS_LOCK = threading.Lock()


def start_job(fn, *args):
    job_id = uuid.uuid4().hex
    with JOBS_LOCK:
        for k in [k for k, j in JOBS.items() if time.time() - j["t"] > 3600]:
            del JOBS[k]
        JOBS[job_id] = {"status": "running", "t": time.time()}

    def work():
        try:
            result = {"status": "done", "result": fn(*args)}
        except CodexError as e:
            result = {"status": "error", "error": str(e)}
        except Exception as e:
            result = {"status": "error", "error": f"{type(e).__name__}: {e}"}
        with JOBS_LOCK:
            JOBS[job_id].update(result)

    threading.Thread(target=work, daemon=True).start()
    return job_id


# ---------------------------------------------------------------- HTTP -----

class Handler(http.server.BaseHTTPRequestHandler):
    server_version = "VideoProjectsAI/1.1"

    def log_message(self, fmt, *args):
        sys.stderr.write("  " + (fmt % args) + "\n")

    # --- helpers ---
    def origin_ok(self):
        origin = self.headers.get("Origin")
        return origin is None or origin in ALLOWED_ORIGINS

    def cors(self):
        origin = self.headers.get("Origin")
        if origin in ALLOWED_ORIGINS:
            self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Vary", "Origin")

    def reply(self, status, body, ctype="application/json; charset=utf-8"):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False).encode()
        self.send_response(status)
        self.cors()
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def error(self, status, message):
        self.reply(status, {"error": {"message": message}})

    def read_body(self):
        length = int(self.headers.get("Content-Length") or 0)
        if length > MAX_BODY:
            raise ValueError("Запрос слишком большой.")
        return self.rfile.read(length) if length else b""

    def forward(self, url, auth, body=None):
        if self.command == "POST" and body is None:
            body = self.read_body()
        req = urllib.request.Request(url, data=body, method=self.command)
        if self.headers.get("Content-Type") and body is not None:
            req.add_header("Content-Type", self.headers["Content-Type"])
        if auth:
            req.add_header("Authorization", auth)
        req.add_header("User-Agent", "VideoProjectsAI/1.1")
        try:
            resp = urllib.request.urlopen(req, timeout=TIMEOUT, context=CTX)
        except urllib.error.HTTPError as e:
            data = e.read()
            return self.reply(e.code, data, e.headers.get("Content-Type", "application/json"))
        except ssl.SSLError as e:
            return self.error(502, f"SSL: {e}. На Mac запусти «Install Certificates.command» из папки Python.")
        except Exception as e:  # network errors
            return self.error(502, f"Нет соединения: {e}")
        with resp:
            self.send_response(resp.status)
            self.cors()
            self.send_header("Content-Type", resp.headers.get("Content-Type", "application/octet-stream"))
            length = resp.headers.get("Content-Length")
            if length:
                self.send_header("Content-Length", length)
            else:
                self.send_header("Connection", "close")
                self.close_connection = True
            self.end_headers()
            while True:
                chunk = resp.read(1 << 16)
                if not chunk:
                    break
                self.wfile.write(chunk)

    def auth_for(self, env_name):
        key = env_key(env_name)
        return ("Bearer " + key) if key else self.headers.get("Authorization")

    # --- routes ---
    def do_OPTIONS(self):
        if not self.origin_ok():
            return self.error(403, "Origin not allowed")
        self.send_response(204)
        self.cors()
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Authorization, Content-Type, X-Ark-Base, X-OpenAI-Via")
        self.send_header("Access-Control-Allow-Private-Network", "true")
        self.send_header("Access-Control-Max-Age", "600")
        self.end_headers()

    def do_GET(self):
        self.route()

    def do_POST(self):
        self.route()

    def route(self):
        if not self.origin_ok():
            return self.error(403, "Origin not allowed")
        path = urllib.parse.urlsplit(self.path)
        if path.path in ("/", "/" + PAGE) and self.command == "GET":
            if path.path == "/":
                self.send_response(302)
                self.send_header("Location", "/" + PAGE)
                self.end_headers()
                return
            with open(os.path.join(ROOT, PAGE), "rb") as f:
                return self.reply(200, f.read(), "text/html; charset=utf-8")
        if path.path == "/api/health":
            return self.reply(200, {"ok": True, "openaiKey": bool(env_key("OPENAI_API_KEY")),
                                    "arkKey": bool(env_key("ARK_API_KEY")), "envFile": bool(ENV_LOADED),
                                    "codex": codex_status()})
        if path.path.startswith("/api/codex/jobs/") and self.command == "GET":
            with JOBS_LOCK:
                job = dict(JOBS.get(path.path.rsplit("/", 1)[-1]) or {})
            if not job:
                return self.error(404, "Задача Codex не найдена — возможно, AI-сервер перезапускали.")
            job.pop("t", None)
            return self.reply(200, job)
        if path.path.startswith("/api/openai/"):
            tail = path.path[len("/api/openai"):]
            if (self.headers.get("X-OpenAI-Via") or "").lower() == "codex":
                return self.codex_route(tail)
            return self.forward(OPENAI + tail + (("?" + path.query) if path.query else ""), self.auth_for("OPENAI_API_KEY"))
        if path.path.startswith("/api/ark/"):
            base = (self.headers.get("X-Ark-Base") or "").rstrip("/")
            if not host_allowed(base, ARK_HOSTS):
                return self.error(400, "Неизвестный адрес платформы Seedance: " + base)
            tail = path.path[len("/api/ark"):]
            return self.forward(base + tail + (("?" + path.query) if path.query else ""), self.auth_for("ARK_API_KEY"))
        if path.path == "/api/fetch" and self.command == "GET":
            url = urllib.parse.parse_qs(path.query).get("url", [""])[0]
            if not host_allowed(url, MEDIA_HOSTS):
                return self.error(400, "Скачивание с этого адреса не разрешено.")
            return self.forward(url, None)
        self.error(404, "Not found")

    def codex_route(self, tail):
        if self.command != "POST":
            return self.error(405, "Codex: только POST.")
        try:
            body = self.read_body()
            ctype = self.headers.get("Content-Type") or ""
            if tail == "/chat/completions":
                job = start_job(codex_chat, json.loads(body or b"{}"))
            elif tail == "/images/generations":
                job = start_job(codex_image, json.loads(body or b"{}"), [])
            elif tail == "/images/edits":
                if not ctype.startswith("multipart/form-data"):
                    return self.error(400, "Codex: ожидается multipart/form-data.")
                fields, files = parse_multipart(ctype, body)
                job = start_job(codex_image, fields, files)
            else:
                return self.error(404, "Codex не умеет " + tail)
        except (ValueError, json.JSONDecodeError) as e:
            return self.error(400, f"Codex: неверный запрос: {e}")
        self.reply(202, {"job": job})


def main():
    server = http.server.ThreadingHTTPServer((HOST, PORT), Handler)
    url = f"http://{HOST}:{PORT}/"
    print(f"AI-сервер запущен: {url}")
    if ENV_LOADED:
        print(f"Из {os.path.basename(ENV_FILE)} взяты: " + ", ".join(ENV_LOADED))
    for name, label in (("OPENAI_API_KEY", "OpenAI"), ("ARK_API_KEY", "Seedance")):
        print(f"  ключ {label}: " + ("есть на сервере" if env_key(name) else "нет — вводится на странице"))
    print("  Codex: " + refresh_codex_status()["message"])
    if EXTRA_ORIGINS:
        print("Разрешённые адреса страницы: " + ", ".join(sorted(EXTRA_ORIGINS)))
    print("Оставь это окно открытым, пока генерируешь кадры и видео. Остановить: Ctrl+C.")
    if "--open" in sys.argv:
        webbrowser.open(url + PAGE)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nОстановлено.")


if __name__ == "__main__":
    main()
