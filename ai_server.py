#!/usr/bin/env python3
"""Local helper for Video_Projects_Local.html.

Forwards AI requests from the page to OpenAI (frames), Seedance / ModelArk and
Higgsfield (video), because browsers may block direct calls to these APIs (CORS).
Listens only on 127.0.0.1 (put Cloudflare Tunnel in front of it on a server,
see deploy/). No dependencies beyond the Python standard library.

    python3 ai_server.py            # then press «Проверить соединение» in the page

Keys: a `.env` file next to this script (see .env.example) or the environment
(OPENAI_API_KEY, ARK_API_KEY, GEMINI_API_KEY, BYTEPLUS_ACCESS_KEY,
BYTEPLUS_SECRET_KEY, BYTEPLUS_TOS_BUCKET, HIGGSFIELD_API_KEY_ID, HIGGSFIELD_API_KEY_SECRET). A key on the server wins over one
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
import io
import struct
import zipfile
import xml.etree.ElementTree as ET

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


# ------------------------------------------------------ ElevenLabs Music ----
# Background music for the ad, exactly as long as the ad: POST /v1/music returns the audio (mp3).
# Key: .env ELEVENLABS_API_KEY or the page's field (header X-Eleven-Key). Paid plans only (Starter+ for
# commercial use), $0.15 per minute.
ELEVEN_API = "https://api.elevenlabs.io/v1/music"
ELEVEN_MODELS = ("music_v2_5", "music_v2", "music_v1")


def eleven_key(typed=None):
    return env_key("ELEVENLABS_API_KEY") or env_key("ELEVEN_API_KEY") or (typed or "").strip()


def eleven_music(key, body):
    prompt = str(body.get("prompt") or "").strip()
    if not prompt:
        raise HFError(400, "Опиши музыку — поле «Описание музыки» пустое.")
    try:
        ms = int(round(float(body.get("seconds") or 30) * 1000))
    except (TypeError, ValueError):
        raise HFError(400, "Неверная длина трека.")
    ms = max(3000, min(300000, ms))
    model = body.get("model") if body.get("model") in ELEVEN_MODELS else ELEVEN_MODELS[0]
    data = {"prompt": prompt[:4000], "music_length_ms": ms, "model_id": model,
            "force_instrumental": bool(body.get("instrumental", True))}
    req = urllib.request.Request(ELEVEN_API + "?output_format=mp3_44100_192", data=json.dumps(data).encode(), method="POST")
    req.add_header("xi-api-key", key)
    req.add_header("Content-Type", "application/json")
    req.add_header("Accept", "audio/mpeg")
    req.add_header("User-Agent", "VideoProjectsAI/1.0")
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT, context=CTX) as resp:
            audio = resp.read()
            ctype = resp.headers.get("Content-Type") or "audio/mpeg"
    except urllib.error.HTTPError as e:
        raw = e.read()
        try:
            detail = json.loads(raw).get("detail")
        except Exception:
            detail = raw.decode("utf-8", "replace")[:300]
        msg = ""
        if isinstance(detail, dict):
            status, data_ = detail.get("status"), detail.get("data") or {}
            if status in ("bad_prompt", "bad_composition_plan"):
                tip = data_.get("prompt_suggestion") or ""
                raise HFError(400, "ElevenLabs отклонил описание: в нём есть исполнитель, группа или песня — опиши звучание "
                                   "словами (жанр, темп, инструменты)." + (" Можно так: " + tip if tip else ""))
            msg = detail.get("message") or status or ""
        elif isinstance(detail, list):
            msg = "; ".join(str(d.get("msg") if isinstance(d, dict) else d) for d in detail)
        else:
            msg = str(detail or "")
        hint = {401: "неверный ключ ElevenLabs.", 402: "на балансе ElevenLabs не хватает средств.",
                403: "ключу не хватает прав или нет платного плана — музыка через API только на платных планах.",
                429: "слишком много запросов или закончился лимит — подожди и повтори."}.get(e.code, "")
        raise HFError(e.code, f"ElevenLabs ({e.code}): " + (hint + " " if hint else "") + (msg[:400] if msg else ""))
    except Exception as e:
        raise HFError(502, f"Нет соединения с ElevenLabs: {e}")
    if len(audio) < 1000:
        raise HFError(502, "ElevenLabs вернул пустой файл.")
    print(f"  ElevenLabs → музыка {ms / 1000:.1f} с ({model})")
    return audio, ctype


# ----------------------------------------------------------- Higgsfield ----
# Video through the Higgsfield API (Kling, Seedance, ...). Paid from the API's own USD balance
# (open.higgsfield.ai → Billing), not from the website plan credits. Keys: .env
# HIGGSFIELD_API_KEY_ID + HIGGSFIELD_API_KEY_SECRET, or "KEY_ID:KEY_SECRET" typed in the page.
# The page sends the scene picture as a data URL; it is uploaded to Higgsfield's storage
# (presigned PUT) because image_url must be a public URL.

HF_API = "https://api.higgsfield.ai"
HF_ENDPOINT = re.compile(r"[a-z0-9][a-z0-9.\-]*(/[a-z0-9][a-z0-9.\-]*){1,4}")
HF_IMAGE = re.compile(r"data:(image/(?:png|jpeg|jpg|webp));base64,(.+)", re.S)
HF_MEDIA = set()  # result URLs Higgsfield returned: /api/fetch downloads only these
HF_MEDIA_LOCK = threading.Lock()


class HFError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status, self.message = status, message


def hf_server_key():
    kid = env_key("HIGGSFIELD_API_KEY_ID") or env_key("HF_API_KEY_ID")
    sec = env_key("HIGGSFIELD_API_KEY_SECRET") or env_key("HF_API_KEY_SECRET")
    if kid and sec:
        return f"{kid}:{sec}"
    return env_key("HIGGSFIELD_API_KEY") or env_key("HF_CREDENTIALS")


def hf_key(typed=None):
    key = hf_server_key()
    if key:
        return key
    typed = (typed or "").strip()
    return typed if re.fullmatch(r"[^:\s]+:[^:\s]+", typed) else ""


def hf_message(code, detail):
    if isinstance(detail, list):
        detail = "; ".join(str(d.get("msg") if isinstance(d, dict) else d) for d in detail)
    detail = str(detail or "").strip()[:500]
    hint = {
        401: "неверный ключ — проверь KEY_ID и KEY_SECRET (open.higgsfield.ai → API Keys).",
        402: "на балансе Higgsfield API не хватает денег — пополни его в open.higgsfield.ai → Billing "
             "(это отдельный баланс, кредиты подписки сайта сюда не идут).",
        403: "доступ запрещён — чаще всего на балансе Higgsfield API не хватает денег: пополни его в "
             "open.higgsfield.ai → Billing (кредиты подписки сайта сюда не идут).",
        404: "такой модели нет или она не включена для этого аккаунта.",
        423: "модель временно недоступна — попробуй позже или выбери другую.",
        429: "очередь аккаунта заполнена или слишком много запросов — подожди минуту и повтори.",
        503: "модель сейчас недоступна — попробуй позже или выбери другую.",
    }.get(code, "")
    return f"Higgsfield ({code}): " + (hint + " " if hint else "") + (f"Ответ: {detail}" if detail else "")


def hf_call(key, method, path, body=None, extra=None, timeout=60):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(HF_API + path, data=data, method=method)
    req.add_header("Authorization", "Key " + key)
    req.add_header("Accept", "application/json")
    req.add_header("User-Agent", "VideoProjectsAI/1.0")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    for k, v in (extra or {}).items():
        req.add_header(k, v)
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=CTX) as resp:
            raw = resp.read()
    except urllib.error.HTTPError as e:
        raw = e.read()
        try:
            detail = json.loads(raw).get("detail")
        except Exception:
            detail = raw.decode("utf-8", "replace")[:300]
        raise HFError(e.code, hf_message(e.code, detail))
    except Exception as e:
        raise HFError(502, f"Нет соединения с Higgsfield: {e}")
    try:
        return json.loads(raw) if raw.strip() else {}
    except ValueError:
        raise HFError(502, "Higgsfield ответил не JSON: " + raw.decode("utf-8", "replace")[:200])


def hf_upload(key, data_url):
    m = HF_IMAGE.fullmatch(data_url.strip())
    if not m:
        raise HFError(400, "Higgsfield: картинка сцены должна быть PNG, JPEG или WebP.")
    ctype = "image/jpeg" if m.group(1) == "image/jpg" else m.group(1)
    try:
        raw = base64.b64decode(m.group(2), validate=False)
    except ValueError:
        raise HFError(400, "Higgsfield: картинка сцены повреждена.")
    up = hf_call(key, "POST", "/files/generate-upload-url", {"content_type": ctype})
    url, public = up.get("upload_url"), up.get("public_url")
    if not url or not public:
        raise HFError(502, "Higgsfield не дал адрес для загрузки картинки.")
    req = urllib.request.Request(url, data=raw, method="PUT")  # presigned: no Higgsfield key here
    for k, v in (up.get("upload_headers") or {"Content-Type": ctype}).items():
        req.add_header(k, str(v))
    try:
        urllib.request.urlopen(req, timeout=120, context=CTX).close()
    except urllib.error.HTTPError as e:
        raise HFError(502, f"Higgsfield: картинка не загрузилась ({e.code}).")
    except Exception as e:
        raise HFError(502, f"Higgsfield: картинка не загрузилась: {e}")
    return public


def hf_video(key, body):
    endpoint = str(body.get("endpoint") or "").strip().strip("/")
    if (not HF_ENDPOINT.fullmatch(endpoint) or "video" not in endpoint
            or endpoint.split("/")[0] in ("requests", "files", "estimate")):
        raise HFError(400, "Неверная модель Higgsfield: " + endpoint)
    args = body.get("args") or {}
    if not isinstance(args, dict):
        raise HFError(400, "Неверные параметры видео.")
    image = str(body.get("image") or "")
    if image.startswith("data:"):
        image = hf_upload(key, image)
    elif not image.startswith("https://"):
        raise HFError(400, "Нет картинки сцены.")
    args = {**args, "image_url": image}
    usd = None
    try:  # price of this exact request; the estimate is free
        usd = hf_call(key, "POST", "/estimate/" + endpoint, args, timeout=20).get("usd")
    except HFError:
        pass
    res = hf_call(key, "POST", "/" + endpoint, args, {"Idempotency-Key": str(uuid.uuid4())})
    rid = str(res.get("request_id") or "")
    if not rid:
        raise HFError(502, "Higgsfield не вернул номер задачи.")
    print(f"  Higgsfield → {endpoint}: задача {rid}" + (f" · ≈ ${usd}" if usd else ""))
    return {"id": rid, "status": res.get("status"), "usd": usd}


def hf_status(key, rid):
    d = hf_call(key, "GET", f"/requests/{urllib.parse.quote(rid)}/status")
    url = (d.get("video") or {}).get("url") if isinstance(d.get("video"), dict) else None
    if isinstance(url, str) and url.startswith("https://"):
        with HF_MEDIA_LOCK:
            HF_MEDIA.add(url)
    return d


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
            files.append((part.get_filename(), data, name))
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
        for i, (_, data, *_rest) in enumerate(refs, 1):
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


# ------------------------------------------------------------ DaVinci -----
# A .drt keeps media as compressed binary records that can't be written blindly,
# so the timeline with footage is built by DaVinci Resolve itself: the server saves
# the scene videos/frames, the titles .drt and a Lua script, installs the script into
# Resolve's Scripts menu, and the script imports the .drt and places each clip on V1.
RESOLVE_SCRIPT_NAME = "Video Projects — собрать таймлайн.lua"
MEDIA_EXT = {"mp4", "mov", "webm", "png", "jpg", "jpeg", "webp"}


def export_root():
    custom = os.environ.get("AI_EXPORT_DIR", "").strip()
    if custom:
        return os.path.expanduser(custom)
    movies = os.path.expanduser("~/Movies")
    return os.path.join(movies, "Video Projects") if os.path.isdir(movies) else os.path.join(ROOT, "export")


def resolve_scripts_dir():
    home = os.path.expanduser("~")
    if sys.platform == "darwin":
        base = os.path.join(home, "Library", "Application Support", "Blackmagic Design", "DaVinci Resolve")
    elif os.name == "nt":
        base = os.path.join(os.environ.get("APPDATA", home), "Blackmagic Design", "DaVinci Resolve", "Support")
    else:
        base = os.path.join(home, ".local", "share", "DaVinciResolve")
    return os.path.join(base, "Fusion", "Scripts", "Utility"), os.path.isdir(os.path.dirname(base)) or os.path.isdir(base)


def lua_str(v):
    return '"' + str(v).replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "") + '"'


def safe_folder_name(name):
    name = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', " ", name or "").strip().strip(".")
    return re.sub(r"\s+", " ", name)[:80] or "Ролик"


def davinci_script(folder, drt, timeline, clips):
    rows = ",\n".join("  {file=%s, record=%d, frames=%d, still=%s}" % (lua_str(c["file"]), c["record"], c["frames"],
                                                                     "true" if c["kind"] == "image" else "false")
                      for c in clips)
    return f"""-- Создано Video Projects. Запуск: DaVinci Resolve → Workspace → Scripts → «Video Projects — собрать таймлайн».
-- Импортирует таймлайн с титрами (.drt) и ставит видео сцен на дорожку V1 по разметке сцен.
local folder = {lua_str(folder)}
local drt = {lua_str(drt)}
local timelineName = {lua_str(timeline)}
local clips = {{
{rows}
}}

local function say(t) print("[Video Projects] " .. t) end
local resolve = resolve or (Resolve and Resolve())
if not resolve then say("Нет связи с DaVinci Resolve.") return end
local project = resolve:GetProjectManager():GetCurrentProject()
if not project then say("Открой или создай проект в DaVinci Resolve и запусти скрипт ещё раз.") return end
local mp = project:GetMediaPool()
local bin = mp:AddSubFolder(mp:GetRootFolder(), timelineName .. " — медиа")
if bin then mp:SetCurrentFolder(bin) end

local tl = mp:ImportTimelineFromFile(drt, {{timelineName = timelineName}})
if not tl then say("Не удалось импортировать титры: " .. drt) return end
project:SetCurrentTimeline(tl)

local paths = {{}}
for i, c in ipairs(clips) do paths[i] = folder .. "/" .. c.file end
local items = mp:ImportMedia(paths) or {{}}
local byName = {{}}
for _, it in pairs(items) do byName[it:GetClipProperty("File Name")] = it end

local infos, missing = {{}}, 0
for _, c in ipairs(clips) do
  local it = byName[c.file]
  if it then
    local n = c.frames
    if not c.still then
      local len = tonumber(it:GetClipProperty("Frames") or "") or n
      if len > 0 and len < n then n = len end
    end
    table.insert(infos, {{mediaPoolItem = it, startFrame = 0, endFrame = n - 1, trackIndex = 1, recordFrame = c.record}})
  else
    missing = missing + 1
    say("Не найден файл: " .. c.file)
  end
end
local placed = mp:AppendToTimeline(infos)
local count = 0
if placed then for _ in pairs(placed) do count = count + 1 end end
say("Готово: таймлайн «" .. timelineName .. "», клипов на V1: " .. count .. (missing > 0 and (", не найдено файлов: " .. missing) or ""))
"""


def davinci_export(fields, files):
    try:
        manifest = json.loads(fields.get("manifest") or "{}")
    except ValueError:
        raise CodexError("Неверный список клипов.")
    by_field = {name: (fname, data) for fname, data, name in files if name}
    if "drt" not in by_field:
        raise CodexError("Нет файла .drt с титрами.")
    name = safe_folder_name(fields.get("name"))
    folder = os.path.join(export_root(), name)
    os.makedirs(folder, exist_ok=True)
    for old in glob.glob(os.path.join(folder, "scene-*")) + glob.glob(os.path.join(folder, "end-card.*")):
        try:
            os.remove(old)
        except OSError:
            pass
    drt_path = os.path.join(folder, name + ".drt")
    with open(drt_path, "wb") as f:
        f.write(by_field["drt"][1])
    clips = []
    for k, c in enumerate(manifest.get("clips") or []):
        part = by_field.get(str(c.get("field")))
        if not part:
            continue
        ext = (os.path.splitext(part[0])[1][1:] or "").lower()
        if ext not in MEDIA_EXT:
            ext = image_kind(part[1]) or "mp4"
        kind = "image" if ext in ("png", "jpg", "jpeg", "webp") else "video"
        base = "end-card" if c.get("field") == "mEnd" else "scene-%02d" % (int(c.get("scene") or k + 1))
        file = f"{base}.{ext}"
        with open(os.path.join(folder, file), "wb") as f:
            f.write(part[1])
        clips.append({"file": file, "record": int(c.get("record") or 0), "frames": max(1, int(c.get("frames") or 1)), "kind": kind})
    if not clips:
        raise CodexError("Нет ни одного видео или картинки сцен.")
    script = davinci_script(folder.replace("\\", "/"), drt_path.replace("\\", "/"), name, clips)
    with open(os.path.join(folder, RESOLVE_SCRIPT_NAME), "w", encoding="utf-8") as f:
        f.write(script)
    scripts_dir, resolve_found = resolve_scripts_dir()
    installed = False
    if resolve_found:
        try:
            os.makedirs(scripts_dir, exist_ok=True)
            with open(os.path.join(scripts_dir, RESOLVE_SCRIPT_NAME), "w", encoding="utf-8") as f:
                f.write(script)
            installed = True
        except OSError:
            pass
    if sys.platform == "darwin":
        subprocess.Popen(["open", folder], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    print(f"  DaVinci: папка {folder} · клипов {len(clips)} · скрипт " + ("в меню Resolve" if installed else "только в папке"))
    return {"folder": folder, "clips": len(clips), "videos": sum(c["kind"] == "video" for c in clips),
            "scriptInstalled": installed, "scriptName": RESOLVE_SCRIPT_NAME[:-4]}


# ------------------------------------------- DaVinci: build and render -----
# One button in the page: the server takes the titles .drt from the page, adds the look of the
# user's reference timeline (the template inside the page) and asks DaVinci Resolve to build a new
# project and render it. Needs Resolve running with Preferences → System → General →
# External scripting using: Local.
#   V1 scene videos (placed by Resolve)      V4 watermark: zoom 20%, bottom right, 70%, fades out
#   V2 adjustment clip: FilmConvert Nitrate  V5 end card: logo on a background, Checker Wipe in,
#      + Gaussian blur grade                     gentle pulse (Fusion comp imported from a file —
#   V3 titles                                    comps built through the API are not rendered)
RESOLVE_API = "/Library/Application Support/Blackmagic Design/DaVinci Resolve/Developer/Scripting"
RESOLVE_LIB = "/Applications/DaVinci Resolve/DaVinci Resolve.app/Contents/Libraries/Fusion/fusionscript.so"
DRT_NS = "ListMgt::"
END_SCALE = 0.34      # end logo size in the reference timeline (Edit zoom)
WIPE_FRAMES = 24      # Checker Wipe into the end card, centred on the last cut
WM_FADE = 6           # watermark fade before the end card covers it
PULSE_FRAMES = 12     # end logo «thump» like a cone on a subwoofer: every 0.5 s (120 BPM at 24 fps)…
PULSE_AMOUNT = 0.018  # …up by 1.8 % in two frames, then a quick fall back


# FilmConvert Nitrate on the adjustment clip, uncompressed (DaVinci keeps it zstd-packed): the reference
# settings with the user's corrections from DaVinci — Exposure −0.4 (the reference −1.56 was too dark),
# Temp 10. Exposure and Temp are set per build from the page settings; the rest stays as it is.
FILMCONVERT_PAYLOAD = (
    "0a16082c38104a08085b1a040a0220034a004a004a004a000a0a0848180638224a004a000ace0608321804381440b2e7c69a"
    "a5314abe06086d10001aea0512e70508d98cbd021223636f6d2e7275626265726d6f6e6b65793a66696c6d636f6e76657274"
    "6e6974726174651a1b4f6678496d616765456666656374436f6e7465787446696c74657220012a220a1c436f6d7061746962"
    "696c6974792056657273696f6e204e756d626572120208062a150a084578706f73757265120911000000a09999d9bf2a180a"
    "0b46696c6d204368726f6d6112091100000040dc114d402a160a0946696c6d204c756d6112091100000060ca9a42402a100a"
    "0a46696c6d2053746f636b120222002a1d0a10477261696e20486967686c696768747312091125068195438be83f2a210a14"
    "477261696e204d696420486967686c696768747312091133333333333325402a1e0a11477261696e204d696420536861646f"
    "7773120911ffffffffffff2c402a1b0a0e477261696e204d6964746f6e65731209110000000000002f402a1a0a0d47726169"
    "6e20536861646f7773120911ae47e17a14ae01402a1b0a0e477261696e20537472656e677468120911000000e02e0249402a"
    "1b0a0e496d61676520536f66746e6573731209110000004063ce18402a0c0a044d616b651204220208022a0d0a054d6f6465"
    "6c1204220208022a350a0f4f534320477261696e20437572766512222a20302e303232317c302e3134357c302e3135357c30"
    "2e3130367c302e30303736372a1b0a15506c7567696e2056657273696f6e204e756d626572120208042a0f0a0750726f6669"
    "6c651204220208022a0f0a0950726f66696c654944120208022a280a225265736f6c7665557365416c706861466f72547261"
    "636b436f6d706f736974696e67120218012a110a0454656d7012091100000000000024402a110a0454696e74120911000000"
    "00000000002a1c0a0f66696c6d5f6e65757472616c69736512091100000000000000002a1c0a0f66696c6d5f736174757261"
    "74696f6e120911000000e08a3a5b402a170a1166696c6d5f73746f636b5f656e61626c65120218012a100a0a68616c5f656e"
    "61626c65120218002249124708d98cbd021223636f6d2e7275626265726d6f6e6b65793a66696c6d636f6e766572746e6974"
    "726174651a1b4f6678496d616765456666656374436f6e7465787446696c7465724800"
)


def fc_set(data, name, value):
    """Replace the double value of one FilmConvert parameter in the protobuf payload."""
    key = b"\x0a" + bytes([len(name)]) + name.encode()
    i = data.find(key)
    j = data.find(b"\x11", i + len(key), i + len(key) + 6) if i >= 0 else -1
    if i < 0 or j < 0:
        raise CodexError("Не найден параметр FilmConvert " + name)
    return data[:j + 1] + struct.pack("<d", float(value)) + data[j + 9:]


def filmconvert_blob(exposure=None, temp=None):
    data = bytes.fromhex(FILMCONVERT_PAYLOAD)
    if exposure is not None:
        data = fc_set(data, "Exposure", max(-4.0, min(2.0, float(exposure))))
    if temp is not None:
        data = fc_set(data, "Temp", max(-100.0, min(100.0, float(temp))))
    return (struct.pack(">II", 2, len(data) + 1) + b"\x80" + data).hex()  # 0x80: uncompressed payload


def page_template():
    with open(os.path.join(ROOT, PAGE), encoding="utf-8") as f:
        m = re.search(r'<script id="template-data" type="application/json">(.*?)</script>', f.read(), re.S)
    meta = json.loads(m.group(1))
    return meta, {e["name"]: base64.b64decode(e["data"]) for e in meta["entries"]}


def drt_parse(data):
    s = data.decode("utf-8").replace(DRT_NS, "ListMgt__")
    if s.startswith("<?xml"):
        s = s.split("\n", 1)[1]
    comment = ""
    m = re.match(r"\s*(<!--.*?-->)\s*", s, re.S)
    if m:
        comment, s = m.group(1), s[m.end():]
    return ET.fromstring(s), comment


def drt_dump(root, comment):
    s = ET.tostring(root, encoding="unicode").replace("ListMgt__", DRT_NS)
    return ('<?xml version="1.0" encoding="UTF-8"?>\n' + (comment + "\n" if comment else "") + s).encode("utf-8")


def drt_kid(e, tag):
    for k in e:
        if k.tag == tag:
            return k
    raise CodexError("В шаблоне таймлайна нет поля " + tag)


def drt_set(e, tag, v):
    drt_kid(e, tag).text = str(v)


def drt_tracks(seq):
    return [drt_kid(el, "Sm2TiTrack") for el in drt_kid(seq, "VideoTrackVec")]


def drt_items(track):
    return [list(el)[0] for el in drt_kid(track, "Items")]


def drt_fresh(elem):
    """Copy of a timeline item with new ids (also in the hex / UTF-16 forms Resolve keeps in blobs)."""
    s = ET.tostring(elem, encoding="unicode")
    for old in set(re.findall(r'DbId="([0-9a-f-]{36})"', s)):
        new = str(uuid.uuid4())
        s = s.replace(old, new).replace(old.encode().hex(), new.encode().hex())
        s = s.replace("".join(f"00{ord(c):02x}" for c in old), "".join(f"00{ord(c):02x}" for c in new))
    return ET.fromstring(s)


def build_look_drt(page_drt, *, start, total, end_frames, with_watermark, with_end, wipe_shift=0, exposure=None,
                   temp=None):
    """Titles .drt from the page + adjustment clip, watermark and end card from the reference timeline."""
    meta, tpl = page_template()
    z = zipfile.ZipFile(io.BytesIO(page_drt))
    files = {n: z.read(n) for n in z.namelist()}
    if meta["seq"] not in files:
        raise CodexError("В файле титров нет таймлайна.")
    seq, seq_c = drt_parse(files[meta["seq"]])
    tv = drt_tracks(drt_parse(tpl[meta["seq"]])[0])
    adj = next(i for i in drt_items(tv[1]) if (drt_kid(i, "Name").text or "") == "Adjustment Clip")
    wm, wm_fade = drt_items(tv[3])[0], drt_items(tv[3])[1]
    wipe = next(i for i in drt_items(tv[0]) if i.tag == "Sm2TiTransition")
    title_fade = next(i for i in drt_items(tv[2]) if i.tag == "Sm2TiTransition")
    v = drt_tracks(seq)
    if len(v) < 5:
        raise CodexError("В шаблоне таймлайна меньше пяти видеодорожек.")

    def put(track, item):
        ET.SubElement(drt_kid(track, "Items"), "Element").append(item)

    end_start = start + total - WIPE_FRAMES // 2 - wipe_shift  # earlier if the last video can't run on under the wipe
    full_end = end_start + end_frames if with_end else start + total
    a = drt_fresh(adj)
    drt_set(a, "Start", start); drt_set(a, "Duration", full_end - start)
    drt_set(a, "EffectFiltersBA", filmconvert_blob(exposure, temp))
    put(v[1], a)
    if with_end and drt_items(v[2]):
        f = drt_fresh(title_fade)   # ends exactly with the last title
        drt_set(f, "Start", start + total - WIPE_FRAMES // 2); drt_set(f, "Duration", WIPE_FRAMES // 2)
        put(v[2], f)
    if with_watermark:
        wm_end = end_start + WIPE_FRAMES if with_end else start + total
        w = drt_fresh(wm)
        drt_set(w, "Start", start); drt_set(w, "Duration", wm_end - start)
        put(v[3], w)
        if with_end:
            f = drt_fresh(wm_fade)
            drt_set(f, "Start", wm_end - WM_FADE); drt_set(f, "Duration", WM_FADE)
            put(v[3], f)
    mp_t, _ = drt_parse(tpl[meta["mainMpPath"]])
    pool = [list(e)[0] for e in drt_kid(mp_t, "MediaVec")]
    white = next(c for c in pool if c.tag == "Sm2MpVideoClip" and drt_kid(c, "Name").text == drt_kid(wm, "Name").text)
    logo = next(c for c in pool if c.tag == "Sm2MpVideoClip" and (drt_kid(c, "Name").text or "").startswith("Victor_"))
    if with_end:
        e = drt_fresh(wm)  # a still clip like the watermark, but showing the end logo, untransformed
        drt_set(e, "Name", drt_kid(logo, "Name").text)
        drt_set(e, "MediaRef", logo.get("DbId"))
        drt_set(e, "EffectFiltersBA", "")
        drt_set(e, "Start", end_start); drt_set(e, "Duration", end_frames)
        t = drt_fresh(wipe)
        drt_set(t, "Start", end_start); drt_set(t, "Duration", WIPE_FRAMES)
        drt_set(t, "AlignmentType", 1); drt_set(t, "Position", 1)  # at the start edge of the clip
        put(v[4], t); put(v[4], e)
    files[meta["seq"]] = drt_dump(seq, seq_c)
    mp, mp_c = drt_parse(files[meta["mainMpPath"]])
    mv = drt_kid(mp, "MediaVec")
    for c in ([white] if with_watermark else []) + ([logo] if with_end else []):
        ET.SubElement(mv, "Element").append(c)
    files[meta["mainMpPath"]] = drt_dump(mp, mp_c)
    out = io.BytesIO()
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as zo:
        for n, b in files.items():
            zo.writestr(n, b)
    return out.getvalue(), drt_kid(wm, "Name").text, drt_kid(logo, "Name").text


def film_number(value):
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def mp4_seconds(data):
    """Duration from the movie header (mvhd) of an MP4/MOV, or None."""
    i = data.find(b"mvhd")
    if i < 4:
        return None
    if data[i + 4] == 1:
        scale, dur = struct.unpack(">IQ", data[i + 24:i + 36])
    else:
        scale, dur = struct.unpack(">II", data[i + 16:i + 24])
    return dur / scale if scale else None


def image_size(data):
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return struct.unpack(">II", data[16:24])
    if data[:2] == b"\xff\xd8":
        i = 2
        while i + 9 < len(data):
            if data[i] != 0xFF:
                i += 1
                continue
            marker, size = data[i + 1], struct.unpack(">H", data[i + 2:i + 4])[0]
            if marker in (0xC0, 0xC1, 0xC2, 0xC3):
                h, w = struct.unpack(">HH", data[i + 5:i + 9])
                return w, h
            i += 2 + size
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP" and data[12:16] == b"VP8X":
        return 1 + int.from_bytes(data[24:27], "little"), 1 + int.from_bytes(data[27:30], "little")
    return None


def hex_rgb(value):
    m = re.fullmatch(r"#?([0-9a-fA-F]{6})", str(value or "").strip())
    v = m.group(1) if m else "ffffff"
    return [int(v[i:i + 2], 16) / 255 for i in (0, 2, 4)]


RESOLVE_AUTOMATION = r'''
import json, os, sys, time
cfg = json.load(open(sys.argv[1], encoding="utf-8"))
def say(**k):
    print(json.dumps(k, ensure_ascii=False)); sys.stdout.flush()
def stop(**k):
    say(**k); sys.stdout.flush(); os._exit(0)   # fusionscript may crash on a normal exit
try:
    import DaVinciResolveScript as dvr
except Exception as e:
    stop(error="Не найдены скрипты DaVinci Resolve (%s). Установлен ли DaVinci Resolve?" % e)
r, deadline = None, time.time() + float(cfg.get("wait") or 5)
while True:   # a DaVinci that is just starting answers after a while
    r = dvr.scriptapp("Resolve")
    if r and r.GetProjectManager() or time.time() > deadline:
        break
    time.sleep(3)
if not r:
    stop(error="DaVinci Resolve не отвечает. Проверь в DaVinci: Preferences → System → General → External scripting using: Local, и нажми ещё раз.")
pm = r.GetProjectManager()


def render(p, folder, out_name):
    r.OpenPage("deliver")
    if not p.SetCurrentRenderFormatAndCodec("mp4", "H264"):
        p.SetCurrentRenderFormatAndCodec("mov", "H264")
    p.SetRenderSettings({"SelectAllFrames": True, "TargetDir": folder, "CustomName": out_name})
    job = p.AddRenderJob()
    if not job or not p.StartRendering([job]):
        stop(error="DaVinci Resolve не начал рендер. Отрендерь проект вручную на вкладке Deliver.")
    last = -1
    while p.IsRenderingInProgress():
        st = p.GetRenderJobStatus(job) or {}
        pct = int(st.get("CompletionPercentage") or 0)
        if pct != last:
            say(note="Рендер в DaVinci: %d%%" % pct); last = pct
        time.sleep(2)
    st = p.GetRenderJobStatus(job) or {}
    if st.get("JobStatus") != "Complete":
        stop(error="Рендер не завершился: %s." % (st.get("JobStatus") or "ошибка"))
    r.OpenPage("edit")
    for ext in ("mp4", "mov"):
        f = os.path.join(folder, out_name + "." + ext)
        if os.path.exists(f):
            return f
    return None


if cfg.get("mode") == "render":   # render what the user has checked (and maybe changed) in DaVinci
    p = pm.GetCurrentProject()
    if not p or p.GetName() != cfg["project"]:
        say(note="Открываю в DaVinci проект «%s»…" % cfg["project"])
        p = pm.LoadProject(cfg["project"])
        if not p:
            stop(error="DaVinci не открыл проект «%s». Открой его сам (File → Project Manager) и нажми «Отрендерить» ещё раз." % cfg["project"])
        time.sleep(2)
    tl = p.GetCurrentTimeline()
    music = os.path.join(cfg["folder"], "music.mp3")
    if tl and os.path.exists(music):   # A1 = the music only (projects built before 10.4 had the clips' sound there)
        a1 = tl.GetItemListInTrack("audio", 1) or []
        extra = [it for it in a1 if not (it.GetName() or "").startswith("music.")]
        if extra:
            tl.DeleteClips(extra, False)
            say(note="Убрала с A1 звук из видео сцен: %d" % len(extra))
        if not any((it.GetName() or "").startswith("music.") for it in (tl.GetItemListInTrack("audio", 1) or [])):
            mpool = p.GetMediaPool()
            got = [c for c in (mpool.GetRootFolder().GetClipList() or []) if (c.GetName() or "").startswith("music.")] or (mpool.ImportMedia([music]) or [])
            if got and mpool.AppendToTimeline([{"mediaPoolItem": got[0], "trackIndex": 1, "recordFrame": tl.GetStartFrame(), "mediaType": 2}]):
                say(note="Поставила музыку на A1")
    pm.SaveProject()
    stop(result={"project": cfg["project"], "video": render(p, cfg["folder"], cfg["outName"])})
if not r.GetCurrentPage():   # just started: the Project Manager is showing, projects can't be created yet
    r.OpenPage("edit"); time.sleep(3)
name, n = cfg["project"], 2
p = pm.CreateProject(name)
for _ in range(10):
    if p or pm.GetProjectListInCurrentFolder() and name in pm.GetProjectListInCurrentFolder():
        break
    time.sleep(2); p = pm.CreateProject(name)
while not p and n < 100:
    name = "%s (%d)" % (cfg["project"], n); n += 1
    p = pm.CreateProject(name)
if not p:
    stop(error="DaVinci Resolve не создал проект.")
say(note="Проект «%s» создан, собираю таймлайн…" % name)
fps = str(cfg["fps"])
for k, v in (("timelineFrameRate", fps), ("timelinePlaybackFrameRate", fps),
             ("timelineResolutionWidth", str(cfg["width"])), ("timelineResolutionHeight", str(cfg["height"]))):
    p.SetSetting(k, v)
mp = p.GetMediaPool()
tl = mp.ImportTimelineFromFile(cfg["drt"], {"timelineName": cfg["timeline"]})
if not tl:
    stop(error="DaVinci Resolve не открыл таймлайн " + cfg["drt"])
p.SetCurrentTimeline(tl)
pool = {c.GetName(): c for c in (mp.GetRootFolder().GetClipList() or [])}
for key, media in (("watermark", cfg.get("wmName")), ("endLogo", cfg.get("endName"))):
    if cfg.get(key) and media in pool and not pool[media].ReplaceClip(cfg[key]):
        say(note="Не удалось подставить файл " + cfg[key])
items = mp.ImportMedia([c["path"] for c in cfg["clips"]]) or []
by_path = {}
for it in items:
    by_path[it.GetClipProperty("File Path")] = it
tl_fps = float(cfg["fps"])
placed, missing, slowed, darkened = [], [], [], []
for k, c in enumerate(cfg["clips"]):   # one by one: a slowed clip must not run into the next one
    it = by_path.get(c["path"])
    if not it:
        missing.append(os.path.basename(c["path"])); continue
    need = c["frames"] + (c.get("extra") or 0)
    length, src_fps = need, tl_fps
    if not c["still"]:
        try:   # «Frames» counts the file's own frames; a 30 fps file is shorter on a 24 fps timeline
            src_fps = float(it.GetClipProperty("FPS") or tl_fps) or tl_fps
            length = int(float(it.GetClipProperty("Frames") or 0) * tl_fps / src_fps)
        except ValueError:
            length = need
        if c.get("extra") and 0 < length < need:
            need = max(c["frames"], length)   # the run-on under the wipe is optional
    take = min(need, length) if length > 0 else need
    # startFrame/endFrame are frames of the file, the end is not included
    src_end = take if c["still"] else min(-(-take * src_fps // tl_fps), int(float(it.GetClipProperty("Frames") or 0)) or 10 ** 9)
    src_end = int(src_end)
    got = mp.AppendToTimeline([{"mediaPoolItem": it, "startFrame": 0, "endFrame": src_end, "trackIndex": 1,
                                "recordFrame": c["record"], "mediaType": 1}]) or []   # picture only, no clip sound
    placed += got
    if got and c.get("darken"):   # a bright scene: white point down (a straight curve to ~85 %) so the titles read
        sl = "%.3f" % float(c["darken"])
        if got[0].SetCDL({"NodeIndex": 1, "Slope": " ".join([sl] * 3), "Offset": "0 0 0", "Power": "1 1 1", "Saturation": 1.0}):
            darkened.append(str(k + 1))
    if got:   # a video of another shape fills the frame (cropped), no black bars
        try:
            got[0].SetProperty("Scaling", r.SCALE_FILL)
        except Exception:
            pass
    if got and take < need:   # shorter than its title: slow it down to fill the title, no black gap
        item = got[0]
        try:
            item.SetProperty("RetimeProcess", r.RETIME_OPTICAL_FLOW)
        except Exception:
            pass
        # ripple lengthens the clip; locked tracks (titles, look, logos) stay where they are
        others = [(t, i) for t in ("video", "audio") for i in range(1, tl.GetTrackCount(t) + 1) if (t, i) != ("video", 1)]
        for t, i in others:
            tl.SetTrackLock(t, i, True)
        item.SetSpeed({"Percentage": 100.0 * item.GetDuration() / need, "RippleTimeline": True})
        for t, i in others:
            tl.SetTrackLock(t, i, False)
        slowed.append("сцена %d: %d%%" % (k + 1, round(100.0 * take / need)))
    if got and got[0].GetDuration() != need and not c["still"]:
        say(note="Сцена %d: клип %d кадров вместо %d" % (k + 1, got[0].GetDuration(), need))
say(note="Видео сцен на таймлайне: %d%s%s%s" % (len(placed), (", не найдены: " + ", ".join(missing)) if missing else "",
      (", замедлены до длины титра — " + ", ".join(slowed)) if slowed else "", (", затемнены светлые: сцены " + ", ".join(darkened)) if darkened else ""))
if cfg.get("endComp"):
    ends = [it for it in (tl.GetItemListInTrack("video", 5) or []) if it.GetMediaPoolItem()]
    if ends:
        end = ends[-1]
        end.AddFusionComp()
        raw = os.path.join(cfg["folder"], "end-card-base.comp")
        end.ExportFusionComp(raw, 1)
        text = open(raw, encoding="utf-8").read()
        i = text.find("MediaOut1 = Saver {")
        j = text.find('SourceOp = "MediaIn1"', i)
        if i < 0 or j < 0:
            say(note="Не удалось настроить заставку в Fusion")
        else:
            text = text[:j] + 'SourceOp = "VPMerge"' + text[j + len('SourceOp = "MediaIn1"'):]
            text = text[:i] + cfg["endComp"] + "\n\t\t" + text[i:]
            comp_path = os.path.join(cfg["folder"], "end-card.comp")
            open(comp_path, "w", encoding="utf-8").write(text)
            end.ImportFusionComp(comp_path)
            names = end.GetFusionCompNameList() or []
            if names:
                end.LoadFusionCompByName(names[-1])
r.OpenPage("edit")
tl.SetCurrentTimecode(tl.GetStartTimecode())
if cfg.get("music"):   # A1 holds only the music, from the start; it was generated as long as the ad
    old = tl.GetItemListInTrack("audio", 1) or []
    if old:
        tl.DeleteClips(old, False)
    got = mp.ImportMedia([cfg["music"]]) or []
    if got:
        if not mp.AppendToTimeline([{"mediaPoolItem": got[0], "trackIndex": 1, "recordFrame": tl.GetStartFrame(), "mediaType": 2}]):
            say(note="Не удалось поставить музыку на A1")
    else:
        say(note="DaVinci не открыл файл музыки")
pm.SaveProject()
out = render(p, cfg["folder"], cfg["outName"]) if cfg.get("render") else None
stop(result={"project": name, "timeline": cfg["timeline"], "video": out, "scenes": len(placed), "missing": missing, "slowed": slowed,
             "darkened": darkened, "music": bool(cfg.get("music"))})
'''


def end_comp_text(logo, width, height, bg):
    size = image_size(logo) or (width, height)
    fit = min(width / size[0], height / size[1])  # like the Edit page: fit the frame, then zoom (Fusion scales the file's pixels)
    r, g, b = hex_rgb(bg)
    return f'''VPBackground = Background {{
			Inputs = {{
				UseFrameFormatSettings = Input {{ Value = 0, }},
				Width = Input {{ Value = {width}, }},
				Height = Input {{ Value = {height}, }},
				TopLeftRed = Input {{ Value = {r:.4f}, }},
				TopLeftGreen = Input {{ Value = {g:.4f}, }},
				TopLeftBlue = Input {{ Value = {b:.4f}, }},
				TopLeftAlpha = Input {{ Value = 1, }},
			}},
		}},
		VPPulse = Transform {{
			Inputs = {{
				Size = Input {{ Expression = "{END_SCALE * fit:.5f}*(1+{PULSE_AMOUNT}*iif(time%{PULSE_FRAMES}<2, (time%{PULSE_FRAMES})/2, (({PULSE_FRAMES}-time%{PULSE_FRAMES})/{PULSE_FRAMES - 2})^3))", }},
				Input = Input {{ SourceOp = "MediaIn1", Source = "Output", }},
			}},
		}},
		VPMerge = Merge {{
			Inputs = {{
				Background = Input {{ SourceOp = "VPBackground", Source = "Output", }},
				Foreground = Input {{ SourceOp = "VPPulse", Source = "Output", }},
			}},
		}},'''


def resolve_running():
    if sys.platform != "darwin":
        return True
    return subprocess.run(["pgrep", "-f", "DaVinci Resolve.app/Contents/MacOS/Resolve"], capture_output=True).returncode == 0


def run_resolve(cfg, folder, note):
    """Run the automation in a separate Python (fusionscript can crash its host) and relay its notes."""
    cfg = dict(cfg, wait=5)
    if not resolve_running():
        if not os.path.isdir("/Applications/DaVinci Resolve/DaVinci Resolve.app"):
            raise CodexError("DaVinci Resolve не найден в «Программах».")
        note("Открываю DaVinci Resolve — это до минуты…")
        subprocess.Popen(["open", "-a", "DaVinci Resolve"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        cfg["wait"] = 150
    cfg_path = os.path.join(folder, "davinci-%s.json" % cfg.get("mode", "build"))
    with open(cfg_path, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=1)
    script = os.path.join(folder, "davinci-build.py")
    with open(script, "w", encoding="utf-8") as f:
        f.write(RESOLVE_AUTOMATION)
    env = dict(os.environ, RESOLVE_SCRIPT_API=RESOLVE_API, RESOLVE_SCRIPT_LIB=RESOLVE_LIB,
               PYTHONPATH=os.path.join(RESOLVE_API, "Modules"))
    if cfg["wait"] < 10:
        note("Подключаюсь к DaVinci Resolve…")
    proc = subprocess.Popen([sys.executable, script, cfg_path], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            stdin=subprocess.DEVNULL, env=env, text=True, encoding="utf-8", errors="replace")
    result, error, tail = None, None, []
    for line in proc.stdout:
        line = line.strip()
        try:
            msg = json.loads(line)
        except ValueError:
            if line:
                tail = (tail + [line])[-5:]
            continue
        if msg.get("note"):
            note(msg["note"])
            print("  DaVinci: " + msg["note"])
        if msg.get("error"):
            error = msg["error"]
        if msg.get("result"):
            result = msg["result"]
    proc.wait()
    if error:
        raise CodexError(error)
    if not result:
        raise CodexError("DaVinci Resolve не ответил. " + " ".join(tail)[-300:])
    return result


def davinci_render(fields, files, note):
    """Render the project the user has checked in DaVinci (with any changes made there)."""
    project, folder = (fields.get("project") or "").strip(), (fields.get("folder") or "").strip()
    root = os.path.realpath(export_root())
    if not project or not folder or not os.path.realpath(folder).startswith(root + os.sep) or not os.path.isdir(folder):
        raise CodexError("Нет собранного проекта — сначала нажми «Собрать в DaVinci».")
    result = run_resolve({"mode": "render", "project": project, "folder": folder,
                          "outName": safe_folder_name(fields.get("name"))}, folder, note)
    if result.get("video") and sys.platform == "darwin":
        subprocess.Popen(["open", "-R", result["video"]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return dict(result, folder=folder)


def davinci_build(fields, files, note):
    """Save the media, build the full .drt and let DaVinci Resolve assemble and render the project."""
    try:
        manifest = json.loads(fields.get("manifest") or "{}")
    except ValueError:
        raise CodexError("Неверный список клипов.")
    by_field = {name: (fname, data) for fname, data, name in files if name}
    if "drt" not in by_field:
        raise CodexError("Нет файла .drt с титрами.")
    fps = int(manifest.get("fps") or 24)
    start, total = int(manifest.get("start") or 86400), int(manifest.get("total") or 0)
    width, height = int(manifest.get("width") or 1920), int(manifest.get("height") or 1080)
    if total < 1 or not (16 <= width <= 8192 and 16 <= height <= 8192):
        raise CodexError("Неверная разметка таймлайна.")
    name = safe_folder_name(fields.get("name"))
    stamp = time.strftime("%Y-%m-%d %H-%M")
    folder = os.path.join(export_root(), name, "DaVinci " + stamp)
    os.makedirs(folder, exist_ok=True)
    clips = []
    scene_clips = manifest.get("clips") or []
    for k, c in enumerate(scene_clips):
        part = by_field.get(str(c.get("field")))
        if not part:
            continue
        ext = (os.path.splitext(part[0])[1][1:] or "").lower()
        if ext not in MEDIA_EXT:
            ext = image_kind(part[1]) or "mp4"
        # a letter after the number: Resolve would join scene-01.png, scene-02.png… into one image sequence
        path = os.path.join(folder, "scene-%02d-clip.%s" % (int(c.get("scene") or k + 1), ext))
        with open(path, "wb") as f:
            f.write(part[1])
        try:
            darken = max(0.5, min(1.0, float(c.get("darken")))) if c.get("darken") else None
        except (TypeError, ValueError):
            darken = None
        clips.append({"path": path, "record": int(c.get("record") or start), "frames": max(1, int(c.get("frames") or 1)),
                      "still": ext in ("png", "jpg", "jpeg", "webp"), "extra": 0, "darken": darken})
    if not clips:
        raise CodexError("Нет ни одного видео или картинки сцен.")
    music = by_field.get("music")
    music_path = ""
    if music:
        music_path = os.path.join(folder, "music." + ((os.path.splitext(music[0])[1][1:] or "mp3").lower()))
        with open(music_path, "wb") as f:
            f.write(music[1])
    logos = {}
    for key in ("watermark", "endLogo"):
        part = by_field.get(key)
        if part:
            ext = image_kind(part[1]) or "png"
            path = os.path.join(folder, ("watermark." if key == "watermark" else "end-logo.") + ext)
            with open(path, "wb") as f:
                f.write(part[1])
            logos[key] = (path, part[1])
    end_frames = max(WIPE_FRAMES, round(float(manifest.get("endSeconds") or 3) * fps))
    with_end = "endLogo" in logos
    wipe_shift = 0
    if with_end:
        clips[-1]["extra"] = WIPE_FRAMES // 2  # the last scene runs on under the wipe…
        last = by_field.get(str(scene_clips[-1].get("field"))) if scene_clips else None
        secs = mp4_seconds(last[1]) if last and not clips[-1]["still"] else None
        if secs:   # …as far as the file allows; the wipe moves earlier by the rest, so no black shows under it
            spare = max(0, int(secs * fps + 1e-6) - clips[-1]["frames"])
            clips[-1]["extra"] = min(WIPE_FRAMES // 2, spare)
            wipe_shift = WIPE_FRAMES // 2 - clips[-1]["extra"]
    drt, wm_name, end_name = build_look_drt(by_field["drt"][1], start=start, total=total, end_frames=end_frames,
                                            with_watermark="watermark" in logos, with_end=with_end, wipe_shift=wipe_shift,
                                            exposure=film_number(fields.get("filmExposure")),
                                            temp=film_number(fields.get("filmTemp")))
    drt_path = os.path.join(folder, name + ".drt")
    with open(drt_path, "wb") as f:
        f.write(drt)
    with open(os.path.join(folder, "titles.drt"), "wb") as f:  # the page's titles only, for checking
        f.write(by_field["drt"][1])
    cfg = {"project": f"{name} {stamp}", "timeline": name, "drt": drt_path, "folder": folder, "fps": fps,
           "width": width, "height": height, "clips": clips, "wmName": wm_name, "endName": end_name,
           "watermark": logos.get("watermark", ("",))[0], "endLogo": logos.get("endLogo", ("",))[0],
           "endComp": end_comp_text(logos["endLogo"][1], width, height, fields.get("endBg")) if with_end else "",
           "render": fields.get("render") == "1", "outName": name, "mode": "build", "music": music_path}
    result = run_resolve(cfg, folder, note)
    result["folder"] = folder
    if not result.get("video") and sys.platform == "darwin":  # bring DaVinci to the front to check the edit
        subprocess.Popen(["open", "-a", "DaVinci Resolve"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if result.get("video") and sys.platform == "darwin":
        subprocess.Popen(["open", "-R", result["video"]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return result


def start_build_job(fields, files, fn=None):
    fn = fn or davinci_build
    job_id = uuid.uuid4().hex
    with JOBS_LOCK:
        JOBS[job_id] = {"status": "running", "t": time.time(), "note": "Готовлю файлы…"}

    def note(text):
        with JOBS_LOCK:
            JOBS[job_id]["note"] = text

    def work():
        try:
            result = {"status": "done", "result": fn(fields, files, note)}
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
        self.send_header("Access-Control-Allow-Headers", "Authorization, Content-Type, X-Ark-Base, X-OpenAI-Via, X-Goog-Api-Key, X-HF-Key, X-Eleven-Key")
        self.send_header("Access-Control-Allow-Private-Network", "true")
        self.send_header("Access-Control-Max-Age", "600")
        self.end_headers()

    def do_GET(self):
        self.route()

    def do_POST(self):
        self.route()

    def route(self):
        _active[0] += 1
        try:
            return self._route()
        finally:
            _active[0] -= 1

    def _route(self):
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
            maybe_pull()
            return self.reply(200, {"ok": True, "openaiKey": bool(env_key("OPENAI_API_KEY")),
                                    "arkKey": bool(env_key("ARK_API_KEY")), "geminiKey": bool(env_key("GEMINI_API_KEY")),
                                    "bpKeys": bool(env_key("BYTEPLUS_ACCESS_KEY") and env_key("BYTEPLUS_SECRET_KEY")),
                                    "tosBucket": bool(env_key("BYTEPLUS_TOS_BUCKET")), "envFile": bool(ENV_LOADED),
                                    "hfKey": bool(hf_server_key()), "elevenKey": bool(eleven_key()), "codex": codex_status(), "pageVersion": page_version(),
                                    "update": _upd["note"]})
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
        if path.path.startswith("/api/hf/"):
            return self.hf_route(path.path)
        if path.path == "/api/eleven/music" and self.command == "POST":
            key = eleven_key(self.headers.get("X-Eleven-Key"))
            if not key:
                return self.error(401, "Нет ключа ElevenLabs: впиши его в «Настройки» → «Музыка» или ELEVENLABS_API_KEY в .env.")
            try:
                audio, ctype = eleven_music(key, json.loads(self.read_body() or b"{}"))
            except HFError as e:
                return self.error(e.status, e.message)
            except ValueError:
                return self.error(400, "Неверный запрос.")
            return self.reply(200, audio, ctype)
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
        if path.path == "/api/davinci/build" and self.command == "POST":
            if self.client_address[0] not in ("127.0.0.1", "::1") or self.headers.get("Cf-Connecting-Ip"):
                return self.error(403, "Сборка в DaVinci работает только с AI-сервером на этом компьютере.")
            ctype = self.headers.get("Content-Type") or ""
            if not ctype.startswith("multipart/form-data"):
                return self.error(400, "Ожидается multipart/form-data.")
            fields, files = parse_multipart(ctype, self.read_body())
            return self.reply(202, {"job": start_build_job(fields, files)})
        if path.path == "/api/davinci/render" and self.command == "POST":
            if self.client_address[0] not in ("127.0.0.1", "::1") or self.headers.get("Cf-Connecting-Ip"):
                return self.error(403, "Рендер в DaVinci работает только с AI-сервером на этом компьютере.")
            try:
                fields = {k: str(v) for k, v in json.loads(self.read_body() or b"{}").items()}
            except (ValueError, AttributeError):
                return self.error(400, "Неверный запрос.")
            return self.reply(202, {"job": start_build_job(fields, [], davinci_render)})
        if path.path == "/api/davinci" and self.command == "POST":
            # Writes into this computer's folders: only for a page on this computer, never through Cloudflare.
            if self.client_address[0] not in ("127.0.0.1", "::1") or self.headers.get("Cf-Connecting-Ip"):
                return self.error(403, "Экспорт с видео работает только с AI-сервером на этом компьютере.")
            try:
                ctype = self.headers.get("Content-Type") or ""
                if not ctype.startswith("multipart/form-data"):
                    return self.error(400, "Ожидается multipart/form-data.")
                fields, files = parse_multipart(ctype, self.read_body())
                return self.reply(200, davinci_export(fields, files))
            except CodexError as e:
                return self.error(400, str(e))
            except (OSError, ValueError) as e:
                return self.error(500, f"Не удалось сохранить файлы: {e}")
        if path.path == "/api/fetch" and self.command == "GET":
            url = urllib.parse.parse_qs(path.query).get("url", [""])[0]
            with HF_MEDIA_LOCK:
                from_hf = url in HF_MEDIA
            if not from_hf and not host_allowed(url, MEDIA_HOSTS):
                return self.error(400, "Скачивание с этого адреса не разрешено.")
            return self.forward(url, None)
        self.error(404, "Not found")

    def hf_route(self, path):
        key = hf_key(self.headers.get("X-HF-Key"))
        if not key:
            return self.error(401, "Нет ключа Higgsfield. Впиши HIGGSFIELD_API_KEY_ID и HIGGSFIELD_API_KEY_SECRET "
                                   "в .env рядом с ai_server.py или ключ в «Настройках» (open.higgsfield.ai → API Keys).")
        try:
            if path == "/api/hf/video" and self.command == "POST":
                return self.reply(200, hf_video(key, json.loads(self.read_body() or b"{}")))
            m = re.fullmatch(r"/api/hf/requests/([A-Za-z0-9_-]{6,100})", path)
            if m and self.command == "GET":
                return self.reply(200, hf_status(key, m.group(1)))
        except HFError as e:
            return self.error(e.status, e.message)
        except ValueError as e:
            return self.error(400, f"Higgsfield: неверный запрос: {e}")
        return self.error(404, "Not found")

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



# --- live updates: refresh the page = newest version, no Terminal, no GitHub ---
# While the server runs it pulls from GitHub when the page asks for /api/health (at most once a
# minute) and every 5 minutes. A changed page is picked up by a page refresh (the page shows a
# notice); a changed ai_server.py restarts the server itself as soon as no generation is running.
_upd = {"last": 0.0, "busy": False, "restart": False, "note": ""}
_upd_lock = threading.Lock()
_active = [0]


def git_bin():
    return shutil.which("git") if os.path.isdir(os.path.join(ROOT, ".git")) else None


def pull_updates():
    git = git_bin()
    if not git or os.environ.get("AI_NO_UPDATE"):
        return
    with _upd_lock:
        if _upd["busy"]:
            return
        _upd.update(busy=True, last=time.time())
    try:
        run = lambda *a: subprocess.run([git, "-C", ROOT, *a], capture_output=True, text=True, timeout=60,
                                        stdin=subprocess.DEVNULL)
        before = run("rev-parse", "HEAD").stdout.strip()
        r = run("pull", "--ff-only", "-q")
        after = run("rev-parse", "HEAD").stdout.strip()
        if r.returncode != 0:
            why = (r.stderr or r.stdout).strip().splitlines()
            _upd["note"] = "обновление не скачалось: " + (why[-1] if why else "ошибка git")
            return
        if after and after != before:
            changed = run("diff", "--name-only", before, after).stdout.split()
            subject = run("log", "-1", "--format=%s").stdout.strip()
            print(f"Скачано обновление: {subject} — обнови страницу (⌘R).")
            _upd["note"] = ""
            if "ai_server.py" in changed:
                _upd["restart"] = True
                print("  обновился и сам AI-сервер — перезапущу его, как только не будет генераций.")
    except Exception as e:
        _upd["note"] = f"обновление не скачалось: {e}"
    finally:
        _upd["busy"] = False


def maybe_pull(min_gap=60):
    if time.time() - _upd["last"] > min_gap:
        threading.Thread(target=pull_updates, daemon=True).start()


def updater_loop():
    while True:
        time.sleep(30)
        maybe_pull(300)
        if _upd["restart"]:
            with JOBS_LOCK:
                running = any(j.get("status") == "running" for j in JOBS.values())
            if not running and _active[0] <= 1:
                print("Перезапускаю AI-сервер с новой версией…")
                sys.stdout.flush()
                os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)]
                         + [a for a in sys.argv[1:] if a != "--no-update"] + ["--no-update"])


def self_update():
    """Double-click = newest version: pull from GitHub before starting.

    Skipped without git, outside a git checkout (e.g. the Ubuntu install in /opt/video),
    with --no-update / AI_NO_UPDATE, or when the pull fails (offline, local edits)."""
    if "--no-update" in sys.argv or os.environ.get("AI_NO_UPDATE"):
        return
    if not os.path.isdir(os.path.join(ROOT, ".git")):
        print("ВНИМАНИЕ: эта папка скачана архивом и сама не обновляется — в ней может быть старая версия.")
        print("  Работай из папки, скачанной через git (например ~/vibe-coding/video), и запускай сервер оттуда.")
        return
    git = shutil.which("git")
    if not git:
        return
    head = lambda: subprocess.run([git, "-C", ROOT, "rev-parse", "HEAD"], capture_output=True, text=True,
                                  timeout=10, stdin=subprocess.DEVNULL).stdout.strip()
    print("Проверяю обновления…")
    try:
        before = head()
        r = subprocess.run([git, "-C", ROOT, "pull", "--ff-only", "-q"], capture_output=True, text=True,
                           timeout=60, stdin=subprocess.DEVNULL)
        after = head()
    except Exception as e:
        print(f"  обновление пропущено: {e}")
        return
    if r.returncode != 0:
        why = (r.stderr or r.stdout).strip().splitlines()
        print("  обновить не получилось" + (": " + why[-1] if why else "") + " — запускаю текущую версию.")
        return
    if after and after != before:
        print("  скачана новая версия — перезапускаю…")
        os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)] + sys.argv[1:] + ["--no-update"])
    print("  версия свежая.")


def stop_old_server():
    """If our own AI server already holds the port, stop it so a double-click restarts with new settings."""
    try:
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        if b'"ok"' not in opener.open(f"http://127.0.0.1:{PORT}/api/health", timeout=3).read():
            return False
        pids = subprocess.run(["lsof", "-ti", f"tcp:{PORT}", "-sTCP:LISTEN"], capture_output=True, text=True,
                              timeout=5).stdout.split()
    except Exception:
        return False
    stopped = False
    for pid in pids:
        if pid.isdigit() and int(pid) != os.getpid():
            try:
                os.kill(int(pid), 15)
                stopped = True
            except OSError:
                pass
    if stopped:
        print("Старый AI-сервер остановлен — запускаю новый.")
        time.sleep(1.5)
    return stopped


def page_version():
    try:
        with open(os.path.join(ROOT, PAGE), encoding="utf-8", errors="replace") as f:
            m = re.search(r"версия (\d+(?:\.\d+)*)", f.read())
        return m.group(1) if m else "?"
    except OSError:
        return "?"


def main():
    self_update()
    print(f"Папка приложения: {ROOT} · версия {page_version()}")
    print(f"  Открывай страницу из этой же папки: {os.path.join(ROOT, PAGE)}")
    url = f"http://{HOST}:{PORT}/"
    try:
        try:
            server = http.server.ThreadingHTTPServer((HOST, PORT), Handler)
        except OSError as e:
            if e.errno not in (48, 98, 10048) or not stop_old_server():
                raise
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
    print("  ключ Higgsfield: " + ("есть на сервере" if hf_server_key() else "нет — вводится на странице"))
    print("  ключ ElevenLabs: " + ("есть на сервере" if eleven_key() else "нет — вводится на странице"))
    print("  Codex: " + refresh_codex_status()["message"])
    if EXTRA_ORIGINS:
        print("Разрешённые адреса страницы: " + ", ".join(sorted(EXTRA_ORIGINS)))
    print("Оставь это окно открытым, пока генерируешь кадры и видео. Остановить: Ctrl+C.")
    if git_bin():
        print("Обновления скачиваются сами: обнови страницу (⌘R), когда она об этом скажет.")
        threading.Thread(target=updater_loop, daemon=True).start()
    if "--open" in sys.argv:
        webbrowser.open(url + PAGE)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nОстановлено.")


if __name__ == "__main__":
    main()
