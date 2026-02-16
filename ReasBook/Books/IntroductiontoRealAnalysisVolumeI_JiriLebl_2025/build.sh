#!/usr/bin/env bash
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

python3 ../../../scripts/gen_project_site.py .
"$LAKE_BIN" exe cache get || true
"$LAKE_BIN" -R -Kenv=dev build SiteSupport.LiterateModule
"$LAKE_BIN" -R -Kenv=dev build Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Book:docs || true
"$LAKE_BIN" exe introductiontorealanalysisvolumei-jirilebl-2025-site
