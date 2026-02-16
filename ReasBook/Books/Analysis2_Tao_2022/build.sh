#!/usr/bin/env bash
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

python3 ../../../scripts/gen_project_site.py .
"$LAKE_BIN" exe cache get || true
"$LAKE_BIN" -R -Kenv=dev build Books.Analysis2_Tao_2022.Book:docs || true
"$LAKE_BIN" exe analysis2-tao-2022-site
