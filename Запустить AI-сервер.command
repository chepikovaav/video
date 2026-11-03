#!/bin/bash
# Двойной щелчок в Finder запускает AI-сервер для Video_Projects_Local.html
cd "$(dirname "$0")" || exit 1
exec python3 ai_server.py
