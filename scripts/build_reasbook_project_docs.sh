#!/usr/bin/env bash

# Build docs for each book/paper root module.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

cd "$ROOT_DIR/ReasBook"
for entry in Books/*/Book.lean Papers/*/Paper.lean; do
  [ -f "$entry" ] || continue
  mod="${entry%.lean}"
  mod="${mod//\//.}"
  echo "[build_reasbook_project_docs] $(date -u +'%Y-%m-%dT%H:%M:%SZ') building ${mod}:docs"
  "$LAKE_BIN" -R -Kenv=dev build "$mod:docs"
done
