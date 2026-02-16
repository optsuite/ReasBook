#!/usr/bin/env bash
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

python3 ../../../scripts/gen_project_site.py .
"$LAKE_BIN" exe cache get || true
"$LAKE_BIN" -R -Kenv=dev build Books.ConvexAnalysis_Rockafellar_1970.Book:docs || true
"$LAKE_BIN" exe convexanalysis-rockafellar-1970-site
