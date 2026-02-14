#!/usr/bin/env bash

# Build Verso site and place API docs at _site/docs.
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

./build.sh

cd ReasBookWeb
python3 scripts/gen_sections.py
"$LAKE_BIN" exe reasbook-site

mkdir -p _site/docs
cp -r ../ReasBook/.lake/build/doc/. _site/docs/
find _site/docs -name "*.trace" -delete || true
find _site/docs -name "*.hash" -delete || true

# Some doc-gen4 outputs may omit a root index page; create a stable landing page.
if [ ! -f _site/docs/index.html ]; then
  cat > _site/docs/index.html <<'EOF'
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>ReasBook Documentation</title>
</head>
<body>
  <h1>ReasBook Documentation</h1>
  <ul>
    <li><a href="./Books/Analysis2_Tao_2022/Chapters/Chap01/section01.html">Analysis II (Tao): Chapter 1 Section 1</a></li>
    <li><a href="./Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section01_part1.html">Convex Analysis (Rockafellar): Chapter 1 Section 1 Part 1</a></li>
    <li><a href="./Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section01.html">Introduction to Real Analysis I (Lebl): Chapter 1 Section 1</a></li>
    <li><a href="./Papers/SmoothMinimization_Nesterov_2004/Sections/section01.html">Nesterov 2004: Section 1</a></li>
    <li><a href="./Papers/OnSomeLocalRings_Maassaran_2025/Sections/section01.html">Maassarani 2025: Section 1</a></li>
  </ul>
</body>
</html>
EOF
fi
