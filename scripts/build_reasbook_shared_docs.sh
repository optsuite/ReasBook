#!/usr/bin/env bash

# Build shared ReasBook API docs.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

echo "[build_reasbook_shared_docs] $(date -u +'%Y-%m-%dT%H:%M:%SZ') building ReasBook:docs"
cd "$ROOT_DIR/ReasBook"
"$LAKE_BIN" -R -Kenv=dev build ReasBook:docs
