#!/usr/bin/env python3
"""Local helper for Video_Projects_Local.html.

Forwards AI requests from the page to OpenAI (frames) and Seedance / ModelArk
(video), because browsers may block direct calls to these APIs (CORS).
Listens only on 127.0.0.1. No dependencies beyond the Python standard library.

    python3 ai_server.py            # then press «Проверить соединение» in the page

Optional: keys can come from the environment instead of the page
(OPENAI_API_KEY, ARK_API_KEY). A key typed in the page takes priority.
"""
import http.server
import json
import re
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
