#!/usr/bin/env bash
# run_all.sh -- build the C++ programs, regenerate every figure of the paper into a temporary directory, recompute
# the data files the figures read, and compare everything with figs/ and data/ (see README.md).
#     bash scripts/run_all.sh            (from paper/ or from anywhere; about 1 minute; exit status 0 iff all agree)
# Needs uv (https://docs.astral.sh/uv/), a C++17 compiler (g++ or clang++ as $CXX) and pdftoppm (poppler) for the
# pixel comparison. The figures are written to $FIGOUT (default: a new temporary directory), never over figs/.
set -euo pipefail
cd "$(dirname "$0")/.."                       # paper/
CXX=${CXX:-g++}
PY=(uv run --no-project --with numpy --with matplotlib==3.11.0 python)
mkdir -p scripts/bin
for prog in sepx mdist lb; do
    "$CXX" -O3 -std=c++17 -o scripts/bin/$prog scripts/$prog.cpp
done
OUT=${FIGOUT:-$(mktemp -d)}
echo "figures -> $OUT"
t0=$(date +%s)
"${PY[@]}" scripts/b3_gen.py
"${PY[@]}" scripts/b7_levels_data.py                       # data/levels_p5.txt (exit 1 if it differs)
"${PY[@]}" scripts/b8_freediag_data.py                     # data/freediag.json (exit 1 if it differs)
"${PY[@]}" scripts/b7_levels.py --out "$OUT"               # fig_levels
"${PY[@]}" scripts/b2_carry.py --out "$OUT"                # fig_carry
"${PY[@]}" scripts/b1_relabel.py --out "$OUT"              # fig_idea_v4, fig_hierarchy_v4, fig_cert_v4
"${PY[@]}" scripts/b3_figs.py --out "$OUT"                 # fig_residue, fig_block
"${PY[@]}" scripts/b8_freediag.py --out "$OUT"             # fig_freediag
"${PY[@]}" scripts/b4_figs.py --out "$OUT"                 # fig_count
"${PY[@]}" scripts/b5_figs.py --out "$OUT" HB bs           # fig_HB_v4, fig_bs_slab_v4, fig_bs_3d_v4
"${PY[@]}" scripts/b6_figs.py --out "$OUT"                 # fig_evidence3d_v4, fig_coverage, fig_B2_v4, fig_automaton_v4
"${PY[@]}" scripts/cut1_figs.py --out "$OUT"               # fig_halfcell_v4, fig_volume_v4
echo "generated in $(( $(date +%s) - t0 )) s"
"${PY[@]}" scripts/figcmp.py "$OUT"
