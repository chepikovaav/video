#!/usr/bin/env python3
"""Local helper for Video_Projects_Local.html.

Forwards AI requests from the page to OpenAI (frames) and Seedance / ModelArk
(video), because browsers may block direct calls to these APIs (CORS).
Listens only on 127.0.0.1 (put Cloudflare Tunnel in front of it on a server,
see deploy/). No dependencies beyond the Python standard library.

    python3 ai_server.py            # then press «Проверить соединение» in the page

Keys: a `.env` file next to this script (see .env.example) or the environment
(OPENAI_API_KEY, ARK_API_KEY, GEMINI_API_KEY, BYTEPLUS_ACCESS_KEY,
BYTEPLUS_SECRET_KEY, BYTEPLUS_TOS_BUCKET). A key on the server wins over one
typed in the page; the page hides key fields the server already has.

ChatGPT via Codex: with the Codex CLI logged in with a ChatGPT account
(`codex login`), the page can send OpenAI work here with `X-OpenAI-Via: codex`.
Text/vision requests run through `codex exec`, frames through Codex's built-in
image tool. These take minutes, so they run as jobs: the request answers
202 {"job": id} and the page polls /api/codex/jobs/<id>.
"""
import base64
import email.parser
import email.policy
import glob
import hashlib
import hmac
import http.server
import json
import re
import shutil
import subprocess
import tempfile
import threading
import time
import uuid
from datetime import datetime, timezone
import os
import ssl
import sys
import urllib.error
import urllib.parse
import urllib.request
import webbrowser

ROOT = os.path.dirname(os.path.abspath(__file__))


def load_dotenv(path):
    """KEY=VALUE lines; a repeated key takes its last value; the real environment wins."""
    values, loaded = {}, []
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
        if value:
            values[key] = value
    for key, value in values.items():
        if not os.environ.get(key):
            os.environ[key] = value
            loaded.append(key)
    return loaded


ENV_FILE = os.environ.get("AI_ENV_FILE") or os.path.join(ROOT, ".env")
ENV_LOADED = load_dotenv(ENV_FILE)

PORT = int(os.environ.get("AI_SERVER_PORT", "8787"))
HOST = os.environ.get("AI_SERVER_HOST", "127.0.0.1")
PAGE = "Video_Projects_Local.html"
OPENAI = "https://api.openai.com/v1"
GEMINI = "https://generativelanguage.googleapis.com"
ARK_HOSTS = (".bytepluses.com", ".volces.com", ".byteplus.com", ".volccdn.com")
MEDIA_HOSTS = ARK_HOSTS + (".openai.com", ".oaiusercontent.com", ".blob.core.windows.net")
AMAZON_HOST = re.compile(r"(^|\.)amazon\.[a-z.]{2,10}$")
AMAZON_SHORT = {"a.co", "amzn.to", "amzn.eu", "amzn.asia"}
BROWSER_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/130.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml",
    "Accept-Language": "en-US,en;q=0.9",
}
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


# --- BytePlus private virtual-portrait library (AIGC assets) -----------------
# Seedance 2.x rejects input images with realistic faces. BytePlus' documented
# route for AI-generated people: put the image in the private asset library as
# an AIGC "virtual portrait" and pass asset://<id> instead of the image.
# Flow: upload to a private TOS bucket -> presigned GET URL -> CreateAsset ->
# poll GetAsset until Active. Management calls need IAM AK/SK (V4 signatures);
# the ModelArk API key is not accepted there.
ARK_OPENAPI_VERSION = "2024-01-01"
_asset_lock = threading.Lock()
_last_create = [0.0]
_groups = {}


class AssetError(Exception):
    pass


def _hm(key, msg):
    return hmac.new(key, msg.encode("utf-8"), hashlib.sha256).digest()


def _q(value, safe="-_.~"):
    return urllib.parse.quote(str(value), safe=safe)


def openapi_headers(ak, sk, host, region, query, body, now, service="ark", session_token=""):
    """BytePlus OpenAPI V4 (HMAC-SHA256), same scheme as BytePlus' ark-mcp signer."""
    date = now.strftime("%Y%m%dT%H%M%SZ")
    short = date[:8]
    payload_hash = hashlib.sha256(body).hexdigest()
    hv = {"content-type": "application/json", "host": host, "x-content-sha256": payload_hash, "x-date": date}
    if session_token:
        hv["x-security-token"] = session_token
    names = sorted(hv)
    canonical = "\n".join([
        "POST", "/", "&".join(f"{_q(k)}={_q(v)}" for k, v in sorted(query.items())),
        "".join(f"{n}:{hv[n].strip()}\n" for n in names), ";".join(names), payload_hash])
    scope = f"{short}/{region}/{service}/request"
    sts = "\n".join(["HMAC-SHA256", date, scope, hashlib.sha256(canonical.encode("utf-8")).hexdigest()])
    key = sk.encode("utf-8")
    for part in (short, region, service, "request"):
        key = _hm(key, part)
    sig = hmac.new(key, sts.encode("utf-8"), hashlib.sha256).hexdigest()
    headers = {"Host": host, "X-Date": date, "X-Content-Sha256": payload_hash, "Content-Type": "application/json",
               "Authorization": f"HMAC-SHA256 Credential={ak}/{scope}, SignedHeaders={';'.join(names)}, Signature={sig}"}
    if session_token:
        headers["X-Security-Token"] = session_token
    return headers


def tos_signature(sk, region, date, canonical):
    """TOS4-HMAC-SHA256, as in BytePlus' official `tos` Python SDK (auth.py)."""
    sts = "\n".join(["TOS4-HMAC-SHA256", date, f"{date[:8]}/{region}/tos/request",
                     hashlib.sha256(canonical.encode("utf-8")).hexdigest()])
    key = sk.encode("utf-8")
    for part in (date[:8], region, "tos", "request"):
        key = _hm(key, part)
    return hmac.new(key, sts.encode("utf-8"), hashlib.sha256).hexdigest()


def tos_request_headers(ak, sk, region, method, host, path, content_type, now):
    date = now.strftime("%Y%m%dT%H%M%SZ")
    hv = {"host": host, "x-tos-date": date}
    if content_type:
        hv["content-type"] = content_type
    names = sorted(hv)
    canonical = "\n".join([method, urllib.parse.quote(path, safe="/~"), "",
                           "".join(f"{n}:{hv[n]}\n" for n in names), ";".join(names), "UNSIGNED-PAYLOAD"])
    sig = tos_signature(sk, region, date, canonical)
    headers = {"Host": host, "Date": date, "x-tos-date": date,
               "Authorization": f"TOS4-HMAC-SHA256 Credential={ak}/{date[:8]}/{region}/tos/request, "
                                f"SignedHeaders={';'.join(names)}, Signature={sig}"}
    if content_type:
        headers["Content-Type"] = content_type
    return headers


def tos_presign_get(ak, sk, region, host, path, expires, now):
    date = now.strftime("%Y%m%dT%H%M%SZ")
    params = {"X-Tos-Algorithm": "TOS4-HMAC-SHA256", "X-Tos-Credential": f"{ak}/{date[:8]}/{region}/tos/request",
              "X-Tos-Date": date, "X-Tos-Expires": str(expires), "X-Tos-SignedHeaders": "host"}
    cqs = "&".join(f"{_q(k)}={_q(v)}" for k, v in sorted(params.items()))
    canonical = "\n".join(["GET", urllib.parse.quote(path, safe="/~"), cqs, f"host:{host}\n", "host", "UNSIGNED-PAYLOAD"])
    params["X-Tos-Signature"] = tos_signature(sk, region, date, canonical)
    return f"https://{host}{urllib.parse.quote(path, safe='/~')}?" + "&".join(
        f"{urllib.parse.quote(k, safe='')}={urllib.parse.quote(v, safe='')}" for k, v in params.items())


def asset_cfg(body):
    c = {
        "ak": (env_key("BYTEPLUS_ACCESS_KEY") or body.get("ak") or "").strip(),
        "sk": (env_key("BYTEPLUS_SECRET_KEY") or body.get("sk") or "").strip(),
        "bucket": (env_key("BYTEPLUS_TOS_BUCKET") or body.get("bucket") or "").strip(),
        "region": (body.get("region") or "ap-southeast-1").strip(),
        "tos": (body.get("tosEndpoint") or "tos-ap-southeast-1.bytepluses.com").strip().replace("https://", "").rstrip("/"),
        "ark": (body.get("arkHost") or "ark.ap-southeast-1.byteplusapi.com").strip().replace("https://", "").rstrip("/"),
        "project": (body.get("project") or "default").strip(),
        "group": (body.get("group") or "video-projects-aigc").strip()[:60],
    }
    if not c["ak"] or not c["sk"]:
        raise AssetError("Нет Access Key / Secret Key BytePlus. Укажи их в настройках приложения.")
    if c["bucket"] and not re.fullmatch(r"[a-z0-9][a-z0-9-]{1,61}[a-z0-9]", c["bucket"]):
        raise AssetError("Имя бакета TOS: только строчные латинские буквы, цифры и дефисы. Без бакета оставь поле пустым.")
    for host in (c["tos"], c["ark"]):
        if not re.fullmatch(r"[a-z0-9.-]+\.(bytepluses|byteplusapi|volces|volcengineapi)\.com", host):
            raise AssetError("Неизвестный адрес BytePlus: " + host)
    return c


def openapi_call(c, action, body):
    payload = json.dumps(body, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    query = {"Action": action, "Version": ARK_OPENAPI_VERSION}
    headers = openapi_headers(c["ak"], c["sk"], c["ark"], c["region"], query, payload, datetime.now(timezone.utc))
    url = f"https://{c['ark']}/?" + "&".join(f"{_q(k)}={_q(v)}" for k, v in sorted(query.items()))
    req = urllib.request.Request(url, data=payload, method="POST", headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=60, context=CTX) as r:
            data = json.loads(r.read() or b"{}")
    except urllib.error.HTTPError as e:
        try:
            data = json.loads(e.read() or b"{}")
        except Exception:
            raise AssetError(f"{action}: HTTP {e.code}")
    err = (data.get("ResponseMetadata") or {}).get("Error")
    if err:
        code, msg = err.get("Code", ""), err.get("Message", "")
        hint = ""
        if "AccessKey" in code or "Signature" in code or "SecretToken" in code:
            hint = " Проверь Access Key и Secret Key."
        elif "AccessDenied" in code or "Forbidden" in code or "NoPermission" in code:
            hint = " У пользователя IAM нет прав: добавь политику ArkFullAccess."
        raise AssetError(f"{action}: {code} {msg}".strip() + hint)
    return data.get("Result") or {}


def tos_put(c, key, data, content_type):
    host = f"{c['bucket']}.{c['tos']}"
    path = "/" + key
    headers = tos_request_headers(c["ak"], c["sk"], c["region"], "PUT", host, path, content_type, datetime.now(timezone.utc))
    req = urllib.request.Request(f"https://{host}{urllib.parse.quote(path, safe='/~')}", data=data, method="PUT", headers=headers)
    try:
        urllib.request.urlopen(req, timeout=120, context=CTX).close()
    except urllib.error.HTTPError as e:
        body = e.read()[:300].decode("utf-8", "replace")
        hint = " Проверь имя бакета, регион и права TOSFullAccess." if e.code in (403, 404) else ""
        raise AssetError(f"TOS PutObject: HTTP {e.code} {body}{hint}")


def tos_delete(c, key):
    host = f"{c['bucket']}.{c['tos']}"
    path = "/" + key
    headers = tos_request_headers(c["ak"], c["sk"], c["region"], "DELETE", host, path, "", datetime.now(timezone.utc))
    try:
        urllib.request.urlopen(urllib.request.Request(f"https://{host}{urllib.parse.quote(path, safe='/~')}", method="DELETE", headers=headers), timeout=30, context=CTX).close()
    except Exception:
        pass


def ensure_group(c):
    cache_key = (c["ak"], c["project"], c["group"])
    if cache_key in _groups:
        return _groups[cache_key]
    res = openapi_call(c, "ListAssetGroups", {"Filter": {"Name": c["group"], "GroupType": "AIGC"}, "MaxResults": 50, "ProjectName": c["project"]})
    gid = next((str(g.get("Id")) for g in res.get("Items") or [] if g.get("Name") == c["group"] and g.get("Id")), "")
    if not gid:
        gid = str(openapi_call(c, "CreateAssetGroup", {"Name": c["group"], "Description": "AI-generated frames from Video Projects", "GroupType": "AIGC", "ProjectName": c["project"]}).get("Id") or "")
    if not gid:
        raise AssetError("Не удалось создать группу портретов.")
    _groups[cache_key] = gid
    return gid


def create_and_wait(c, gid, url, name):
    with _asset_lock:  # CreateAsset: 3 calls per minute on the Entry tier
        wait = _last_create[0] + 21 - time.time()
        if wait > 0:
            time.sleep(wait)
        _last_create[0] = time.time()
        aid = str(openapi_call(c, "CreateAsset", {"GroupId": gid, "URL": url, "AssetType": "Image",
                                                  "Name": (name or "frame")[:60], "ProjectName": c["project"]}).get("Id") or "")
    if not aid:
        raise AssetError("CreateAsset не вернул ID.")
    deadline = time.time() + 180
    status = ""
    while time.time() < deadline:
        info = openapi_call(c, "GetAsset", {"Id": aid, "ProjectName": c["project"]})
        status = str(info.get("Status") or "")
        if status == "Active":
            return aid
        if status == "Failed":
            raise AssetError("BytePlus не принял картинку как AI-портрет (Failed). " + json.dumps(info.get("Moderation") or info.get("Error") or {}, ensure_ascii=False)[:300])
        time.sleep(3)
    raise AssetError(f"Портрет не стал активным за 3 минуты (статус {status or 'неизвестен'}). ID: {aid}")


def register_asset(body):
    """Without a bucket the image goes inline as a data: URL (TOS needs enterprise
    certification on personal accounts); with a bucket — via a presigned TOS link."""
    c = asset_cfg(body)
    b64 = (body.get("image") or "").strip()
    raw = base64.b64decode(b64, validate=False)
    if not raw:
        raise AssetError("Пустая картинка.")
    mime = body.get("mime") or "image/jpeg"
    gid = ensure_group(c)
    if not c["bucket"]:
        try:
            aid = create_and_wait(c, gid, f"data:{mime};base64,{b64}", body.get("name"))
        except AssetError as e:
            if re.search(r"URL|InvalidParameter|scheme|protocol", str(e), re.I):
                raise AssetError("BytePlus не принимает картинку без ссылки (" + str(e)[:200] + "). Загрузи кадр в консоли вручную и впиши Asset ID в сцене, или подключи бакет.")
            raise
        return {"assetId": aid, "status": "Active", "groupId": gid, "via": "inline"}
    ext = {"image/png": "png", "image/webp": "webp"}.get(mime, "jpg")
    key = f"video-projects/{uuid.uuid4().hex}.{ext}"
    tos_put(c, key, raw, mime)
    try:
        url = tos_presign_get(c["ak"], c["sk"], c["region"], f"{c['bucket']}.{c['tos']}", "/" + key, 3600, datetime.now(timezone.utc))
        return {"assetId": create_and_wait(c, gid, url, body.get("name")), "status": "Active", "groupId": gid, "via": "tos"}
    finally:
        tos_delete(c, key)


def check_assets(body):
    c = asset_cfg(body)
    out = {}
    try:
        openapi_call(c, "ListAssetGroups", {"Filter": {"GroupType": "AIGC"}, "MaxResults": 10, "ProjectName": c["project"]})
        out["ark"] = "ok"
    except AssetError as e:
        out["ark"] = str(e)
    if out["ark"] != "ok":
        return out
    if c["bucket"]:
        key = f"video-projects/check-{uuid.uuid4().hex}.txt"
        try:
            tos_put(c, key, b"ok", "text/plain")
            tos_delete(c, key)
            out["tos"] = "ok"
        except AssetError as e:
            out["tos"] = str(e)
        return out
    # No bucket: try registering a small test picture inline, then remove it.
    if body.get("testImage"):
        try:
            res = register_asset({**body, "image": body["testImage"], "mime": "image/jpeg", "name": "connection-check"})
            out["inline"] = "ok"
            try:
                openapi_call(c, "DeleteAsset", {"Id": res["assetId"], "ProjectName": c["project"]})
            except AssetError:
                pass
        except AssetError as e:
            out["inline"] = str(e)
    return out


# ---------------------------------------------------------------- Codex ----

CODEX_TIMEOUT = int(os.environ.get("CODEX_TIMEOUT", "600"))
CODEX_EFFORT = os.environ.get("CODEX_EFFORT", "low")
CODEX_MODEL = os.environ.get("CODEX_MODEL", "").strip()
CODEX_SLOTS = threading.BoundedSemaphore(max(1, int(os.environ.get("CODEX_PARALLEL", "2"))))
CODEX_HOME = os.environ.get("CODEX_HOME") or os.path.expanduser("~/.codex")
IMAGE_EXT = (".png", ".jpg", ".jpeg", ".webp")
CODEX_MAX_REFS = 5


_warned_bin = []


def find_codex():
    explicit = os.path.expanduser(os.environ.get("CODEX_BIN", "").strip())
    if explicit and os.path.isfile(explicit):
        return explicit
    if explicit and not _warned_bin:
        _warned_bin.append(explicit)
        print(f"  CODEX_BIN={explicit}: такого файла нет, ищу Codex сам")
    found = shutil.which("codex")
    if found:
        return found
    # Finder-launched .command files often miss Homebrew / npm paths.
    home = os.path.expanduser("~")
    candidates = [home + "/.local/bin/codex", "/opt/homebrew/bin/codex", "/usr/local/bin/codex",
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


def codex_chat(payload, want_json=True):
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
                  + ("\n\nОтветь только JSON-объектом, без пояснений и без ```." if want_json else ""))
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


def codex_responses(payload):
    """OpenAI responses request (plain text input) -> text answer in the responses shape."""
    data = payload.get("input")
    messages = [{"role": "user", "content": data}] if isinstance(data, str) else (data or [])
    text = codex_chat({"messages": messages}, want_json=False)["choices"][0]["message"]["content"]
    return {"object": "response", "output": [{"type": "message", "role": "assistant",
                                              "content": [{"type": "output_text", "text": text}]}]}


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
            if len(names) == CODEX_MAX_REFS:  # Codex's image tool takes at most 5; the page sends the most important first
                break
        size = fields.get("size") or "1024x1536"
        try:
            w, h = (int(x) for x in size.split("x"))
            shape = "vertical" if h > w else "horizontal" if w > h else "square"
        except ValueError:
            shape = "as described"
        # Codex is an agent: left alone it rewrites and shortens the prompt before calling its image
        # tool, and the exact rules about the product's logo and inscriptions get lost. So the prompt
        # goes in markers and must be passed on verbatim; the log below shows what really reached the tool.
        body = (fields.get("prompt") or "").strip() + f"\nImage size: {size} ({shape})."
        prompt = ("Use your built-in image generation tool ($imagegen) exactly once to create one image.\n"
                  "The tool's prompt must be EXACTLY the text between <<<PROMPT and PROMPT>>> below, copied character "
                  "for character: do not shorten, summarize, rephrase, reorder, translate or add anything — every "
                  "sentence about the product, its logo and its inscriptions matters.\n"
                  + (f"Pass num_last_images_to_include:{len(names)} so all {len(names)} attached images reach the tool "
                     "in the attached order (the prompt refers to them as reference image 1, 2, …).\n" if names else "")
                  + f"If the tool has a size or aspect setting, use {size}.\n"
                  "Do not write scripts and do not draw the image with code. After the call, save the generated image "
                  "as out.png in the current working directory and reply only with the file name.\n\n"
                  "<<<PROMPT\n" + body + "\nPROMPT>>>")
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
        call = tool_call_info(log)
        if call:
            sent, n_refs = call.get("prompt", ""), call.get("refs")
            full = sent.strip().startswith(body[:200].strip()) and len(sent) >= len(body) * 0.97
            print(f"  Codex → картинка: промпт {'передан полностью' if full else 'ИЗМЕНЁН агентом'} "
                  f"({len(sent)} из {len(body)} символов), референсов: {n_refs if n_refs is not None else '?'} из {len(names)}")
        if not found:
            raise error or CodexError("Codex не создал картинку: " + log_tail(log))
        with open(found, "rb") as f:
            data = f.read()
        return {"created": int(time.time()), "data": [{"b64_json": base64.b64encode(data).decode()}],
                "codex": {"toolPrompt": (call or {}).get("prompt", "")[:20000], "refsSent": len(names),
                          "refsUsed": (call or {}).get("refs")}}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def tool_call_info(log):
    """What Codex really passed to its image tool, read from the session rollout (best effort)."""
    try:
        with open(log, encoding="utf-8", errors="replace") as f:
            m = re.search(r'"thread_id"\s*:\s*"([^"]+)"', f.read())
    except OSError:
        return None
    if not m:
        return None
    files = glob.glob(os.path.join(CODEX_HOME, "sessions", "**", f"*{m.group(1)}*.jsonl"), recursive=True)
    best = None

    def visit(node):
        nonlocal best
        if isinstance(node, dict):
            for key in ("arguments", "input"):
                raw = node.get(key)
                if isinstance(raw, str) and "prompt" in raw:
                    try:
                        raw = json.loads(raw)
                    except ValueError:
                        continue
                if isinstance(raw, dict) and isinstance(raw.get("prompt"), str):
                    if not best or len(raw["prompt"]) > len(best["prompt"]):
                        best = {"prompt": raw["prompt"], "refs": raw.get("num_last_images_to_include")}
            for v in node.values():
                visit(v)
        elif isinstance(node, list):
            for v in node:
                visit(v)

    for path in files[:1]:
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                for line in f:
                    if '"prompt' in line:
                        try:
                            visit(json.loads(line))
                        except ValueError:
                            pass
        except OSError:
            pass
    return best


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
        if ctype.startswith("text/html"):
            self.send_header("Cache-Control", "no-store")  # always the newest page from this folder
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

    def auth_for(self, env_name):
        key = env_key(env_name)
        return ("Bearer " + key) if key else self.headers.get("Authorization")

    def forward(self, url, auth, extra=None):
        body = self.read_body() if self.command == "POST" else None
        req = urllib.request.Request(url, data=body, method=self.command)
        if self.headers.get("Content-Type") and body is not None:
            req.add_header("Content-Type", self.headers["Content-Type"])
        if auth:
            req.add_header("Authorization", auth)
        for k, v in (extra or {}).items():
            if v:
                req.add_header(k, v)
        req.add_header("User-Agent", "VideoProjectsAI/1.0")
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

    def amazon_page(self, url):
        """Fetch an Amazon product page (HTML only) for the page to parse."""
        def is_amazon(u):
            p = urllib.parse.urlsplit(u)
            host = (p.hostname or "").lower()
            return p.scheme in ("http", "https") and (bool(AMAZON_HOST.search(host)) or host in AMAZON_SHORT)
        if not is_amazon(url):
            return self.error(400, "Нужна ссылка на страницу товара Amazon.")
        req = urllib.request.Request(url, headers=BROWSER_HEADERS)
        try:
            with urllib.request.urlopen(req, timeout=30, context=CTX) as resp:
                if not is_amazon(resp.geturl()):
                    return self.error(400, "Ссылка ведёт не на Amazon.")
                body = resp.read(6 * 1024 * 1024)
                charset = resp.headers.get_content_charset() or "utf-8"
        except urllib.error.HTTPError as e:
            return self.error(502, f"Amazon ответил {e.code}.")
        except Exception as e:
            return self.error(502, f"Нет соединения с Amazon: {e}")
        html = body.decode(charset, errors="replace")
        if "captcha" in html.lower() and "productTitle" not in html:
            return self.error(503, "Amazon показал проверку «я не робот».")
        self.reply(200, html.encode("utf-8"), "text/html; charset=utf-8")

    # --- routes ---
    def do_OPTIONS(self):
        if not self.origin_ok():
            return self.error(403, "Origin not allowed")
        self.send_response(204)
        self.cors()
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Authorization, Content-Type, X-Ark-Base, X-OpenAI-Via, X-Goog-Api-Key")
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
                                    "arkKey": bool(env_key("ARK_API_KEY")), "geminiKey": bool(env_key("GEMINI_API_KEY")),
                                    "bpKeys": bool(env_key("BYTEPLUS_ACCESS_KEY") and env_key("BYTEPLUS_SECRET_KEY")),
                                    "tosBucket": bool(env_key("BYTEPLUS_TOS_BUCKET")), "envFile": bool(ENV_LOADED),
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
        if path.path.startswith("/api/gemini/"):
            tail = path.path[len("/api/gemini"):]
            if not tail.startswith("/v1beta/"):
                return self.error(400, "Неизвестный адрес Gemini.")
            key = env_key("GEMINI_API_KEY") or self.headers.get("X-Goog-Api-Key")
            return self.forward(GEMINI + tail + (("?" + path.query) if path.query else ""), None, {"x-goog-api-key": key})
        if path.path.startswith("/api/ark/"):
            base = (self.headers.get("X-Ark-Base") or "").rstrip("/")
            if not host_allowed(base, ARK_HOSTS):
                return self.error(400, "Неизвестный адрес платформы Seedance: " + base)
            tail = path.path[len("/api/ark"):]
            return self.forward(base + tail + (("?" + path.query) if path.query else ""), self.auth_for("ARK_API_KEY"))
        if path.path in ("/api/asset/check", "/api/asset/register", "/api/asset/delete") and self.command == "POST":
            try:
                body = json.loads(self.rfile.read(int(self.headers.get("Content-Length") or 0)) or b"{}")
                if path.path.endswith("/check"):
                    return self.reply(200, check_assets(body))
                if path.path.endswith("/register"):
                    return self.reply(200, register_asset(body))
                c = asset_cfg(body)
                openapi_call(c, "DeleteAsset", {"Id": str(body.get("assetId") or ""), "ProjectName": c["project"]})
                return self.reply(200, {"ok": True})
            except AssetError as e:
                return self.error(400, str(e))
            except Exception as e:
                return self.error(502, f"Ошибка библиотеки портретов: {e}")
        if path.path == "/api/page" and self.command == "GET":
            return self.amazon_page(urllib.parse.parse_qs(path.query).get("url", [""])[0])
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
            elif tail == "/responses":
                job = start_job(codex_responses, json.loads(body or b"{}"))
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
    url = f"http://{HOST}:{PORT}/"
    try:
        server = http.server.ThreadingHTTPServer((HOST, PORT), Handler)
    except OSError as e:
        if e.errno not in (48, 98, 10048):  # address already in use (macOS, Linux, Windows)
            raise
        print(f"Порт {PORT} уже занят — AI-сервер, скорее всего, уже запущен в другом окне Терминала.")
        print("Чтобы применить новый .env, закрой то окно (или Ctrl+C в нём) и запусти сервер снова.")
        print(f"Остановить сервер без окна: lsof -ti tcp:{PORT} | xargs kill")
        try:
            input("\nНажми Enter, чтобы закрыть это окно.")
        except EOFError:
            pass
        sys.exit(1)
    print(f"AI-сервер запущен: {url}")
    if ENV_LOADED:
        print(f"Из {os.path.basename(ENV_FILE)} взяты: " + ", ".join(ENV_LOADED))
    for name, label in (("OPENAI_API_KEY", "OpenAI"), ("GEMINI_API_KEY", "Gemini"), ("ARK_API_KEY", "Seedance"),
                        ("BYTEPLUS_ACCESS_KEY", "BytePlus AK/SK")):
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
