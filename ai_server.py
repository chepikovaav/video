#!/usr/bin/env python3
"""Local helper for Video_Projects_Local.html.

Forwards AI requests from the page to OpenAI (frames) and Seedance / ModelArk
(video), because browsers may block direct calls to these APIs (CORS).
Listens only on 127.0.0.1. No dependencies beyond the Python standard library.

    python3 ai_server.py            # then press «Проверить соединение» in the page

Optional: keys can come from the environment instead of the page
(OPENAI_API_KEY, ARK_API_KEY). A key typed in the page takes priority.
"""
import base64
import hashlib
import hmac
import http.server
import json
import re
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

PORT = int(os.environ.get("AI_SERVER_PORT", "8787"))
ROOT = os.path.dirname(os.path.abspath(__file__))
PAGE = "Video_Projects_Local.html"
OPENAI = "https://api.openai.com/v1"
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
ALLOWED_ORIGINS = {"null", f"http://127.0.0.1:{PORT}", f"http://localhost:{PORT}"}
TIMEOUT = 600


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
        "ak": (body.get("ak") or os.environ.get("BYTEPLUS_ACCESS_KEY") or "").strip(),
        "sk": (body.get("sk") or os.environ.get("BYTEPLUS_SECRET_KEY") or "").strip(),
        "bucket": (body.get("bucket") or os.environ.get("BYTEPLUS_TOS_BUCKET") or "").strip(),
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


class Handler(http.server.BaseHTTPRequestHandler):
    server_version = "VideoProjectsAI/1.0"

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

    def forward(self, url, auth, stream=False):
        body = None
        if self.command == "POST":
            length = int(self.headers.get("Content-Length") or 0)
            body = self.rfile.read(length)
        req = urllib.request.Request(url, data=body, method=self.command)
        if self.headers.get("Content-Type") and body is not None:
            req.add_header("Content-Type", self.headers["Content-Type"])
        if auth:
            req.add_header("Authorization", auth)
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
        self.send_header("Access-Control-Allow-Headers", "Authorization, Content-Type, X-Ark-Base")
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
            return self.reply(200, {"ok": True, "openaiKey": bool(os.environ.get("OPENAI_API_KEY")),
                                    "arkKey": bool(os.environ.get("ARK_API_KEY"))})
        if path.path.startswith("/api/openai/"):
            auth = self.headers.get("Authorization") or (
                "Bearer " + os.environ["OPENAI_API_KEY"] if os.environ.get("OPENAI_API_KEY") else None)
            tail = path.path[len("/api/openai"):]
            return self.forward(OPENAI + tail + (("?" + path.query) if path.query else ""), auth)
        if path.path.startswith("/api/ark/"):
            base = (self.headers.get("X-Ark-Base") or "").rstrip("/")
            if not host_allowed(base, ARK_HOSTS):
                return self.error(400, "Неизвестный адрес платформы Seedance: " + base)
            auth = self.headers.get("Authorization") or (
                "Bearer " + os.environ["ARK_API_KEY"] if os.environ.get("ARK_API_KEY") else None)
            tail = path.path[len("/api/ark"):]
            return self.forward(base + tail + (("?" + path.query) if path.query else ""), auth)
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


def main():
    server = http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    url = f"http://127.0.0.1:{PORT}/"
    print(f"AI-сервер запущен: {url}")
    print("Оставь это окно открытым, пока генерируешь кадры и видео. Остановить: Ctrl+C.")
    if "--open" in sys.argv:
        webbrowser.open(url + PAGE)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nОстановлено.")


if __name__ == "__main__":
    main()
