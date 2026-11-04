#!/bin/bash
# Установка на Ubuntu: sudo bash deploy/install.sh https://video.example.com
set -euo pipefail
ORIGIN="${1:?Укажи адрес сайта, например https://video.example.com}"
SRC="$(cd "$(dirname "$0")/.." && pwd)"

apt-get update -y && apt-get install -y python3
id video >/dev/null 2>&1 || useradd --system --no-create-home --shell /usr/sbin/nologin video

mkdir -p /opt/video
install -m 644 "$SRC/Video_Projects_Local.html" /opt/video/
install -m 755 "$SRC/ai_server.py" /opt/video/

if [ ! -f /etc/video-ai.env ]; then
  sed "s#^AI_ALLOWED_ORIGINS=.*#AI_ALLOWED_ORIGINS=${ORIGIN%/}#" "$SRC/deploy/video-ai.env.example" > /etc/video-ai.env
  chmod 600 /etc/video-ai.env
fi
install -m 644 "$SRC/deploy/video-ai.service" /etc/systemd/system/video-ai.service
systemctl daemon-reload
systemctl enable --now video-ai
systemctl restart video-ai
sleep 1
curl -fsS http://127.0.0.1:8787/api/health && echo && echo "Готово: сервер работает на 127.0.0.1:8787"
