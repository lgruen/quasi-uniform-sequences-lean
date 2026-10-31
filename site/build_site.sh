#!/bin/sh
# Assemble the website of the repository (GitHub Pages; see .github/workflows/pages.yml):
#   OUT/index.html        landing page
#   OUT/paper.pdf         paper/main.pdf
#   OUT/explainers/       the explainer pages (self-contained HTML; explainers/index.html is the overview)
# usage: site/build_site.sh [OUT=_site]        (POSIX sh; no network access, no build tools)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:-_site}
rm -rf "$OUT"
mkdir -p "$OUT/explainers"
cp "$ROOT/paper/main.pdf" "$OUT/paper.pdf"
for f in "$ROOT"/explainers/*.html; do
  cp "$f" "$OUT/explainers/$(basename "$f")"
done
cat > "$OUT/index.html" <<HTML
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Quasi-uniform digital sequences</title>
<style>
:root { --bg: #ffffff; --ink: #15191f; --muted: #586271; --accent: #2b6cb0; }
@media (prefers-color-scheme: dark) { :root { --bg: #15191f; --ink: #e8ebef; --muted: #a3acb8; --accent: #7fb0e6; } }
body { background: var(--bg); color: var(--ink); font: 17px/1.55 Georgia, "Times New Roman", serif;
       max-width: 44rem; margin: 2.5rem auto; padding: 0 16px; }
a { color: var(--accent); }
li { margin: 0.35em 0; }
</style>
</head>
<body>
<h1>Low-discrepancy quasi-uniform digital sequences in every dimension</h1>
<p>Leonhard Gruenschloss · version 1</p>
<p>In dimension two and higher no Halton-type, Sobol', classical Niederreiter or Faure sequence is quasi-uniform; one
fixed linear scramble of a generalized Faure sequence, built from the residues of one rational function, gives explicit
quasi-uniform digital (0, s)-sequences for every dimension s and every prime base p &gt; 2<sup>s</sup>. The results are
formalized in Lean&nbsp;4 and checked by Comparator with two kernels.</p>
<ul>
<li><a href="paper.pdf">Paper (PDF)</a></li>
<li><a href="explainers/index.html">Explainers</a> (step by step, in progress)</li>
<li><a href="https://github.com/lgruen/quasi-uniform-sequences-lean">Source repository</a> (paper, Lean project, data archive)</li>
<li>Companion: <a href="https://lgruen.github.io/separated-nets-lean/">Low-discrepancy quasi-uniform digital nets in every dimension</a></li>
</ul>
</body>
</html>
HTML
echo "site: $OUT ($(find "$OUT" -type f | wc -l | tr -d ' ') files)"
