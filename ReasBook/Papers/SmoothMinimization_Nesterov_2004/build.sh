#!/usr/bin/env bash
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

python3 ../../../scripts/gen_project_site.py .
"$LAKE_BIN" exe cache get || true
"$LAKE_BIN" -R -Kenv=dev build Papers.SmoothMinimization_Nesterov_2004.Paper:docs || true
"$LAKE_BIN" exe smoothminimization-nesterov-2004-site
