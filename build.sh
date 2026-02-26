#!/usr/bin/env bash

# Build the main Lean project. Set BUILD_DOCS=0 to skip doc-gen4.
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"
BUILD_DOCS="${BUILD_DOCS:-1}"

log() {
  echo "[build.sh] $(date -u +'%Y-%m-%dT%H:%M:%SZ') $*"
}

cd ReasBook
log "running cache get"
"$LAKE_BIN" exe cache get || true
if [ "$BUILD_DOCS" = "1" ]; then
  log "building ReasBook:docs"
  "$LAKE_BIN" -R -Kenv=dev build ReasBook:docs
  # Build docs for every book/paper root module without hardcoding names.
  for entry in Books/*/Book.lean Papers/*/Paper.lean; do
    [ -f "$entry" ] || continue
    mod="${entry%.lean}"
    mod="${mod//\//.}"
    log "building ${mod}:docs"
    "$LAKE_BIN" -R -Kenv=dev build "$mod:docs"
  done
fi
log "building main project"
"$LAKE_BIN" build
log "build complete"
