#!/bin/bash
# Comparator run of one or more configurations, in the foreground, one after the other:
#   scripts/run_comparator.sh <tools dir> comparatorHeadlineSeqV4.json [comparatorGeoSeqV9.json ...]
# <tools dir> holds comparator/, lean4export-rc3/, nanoda_lib/ (Comparator, lean4export at the toolchain's tag, and
# NanoDa, built as described in COMPARATOR_RESULTS.md); `landrun` is replaced by scripts/fake-landrun.sh (macOS has no
# Landlock; no sandbox). Build the modules first (`lake build`, see README.md), otherwise Comparator builds them.
# Writes comparator_<config>.log (full output) and appends one line per configuration to comparator_runs.txt.
set -u
T=${1:?tools dir}; shift
L=$(cd "$(dirname "$0")/.." && pwd)
cd "$L"
mkdir -p "$L/.lake/landrunbin"
ln -sf "$L/scripts/fake-landrun.sh" "$L/.lake/landrunbin/landrun"
rc_all=0
for CFG in "$@"; do
  tag=$(basename "$CFG" .json)
  LOG="$L/comparator_$tag.log"
  N=$(python3 -c "import json,sys; print(len(json.load(open(sys.argv[1]))['theorem_names']))" "$CFG")
  START=$(date +%s)
  PATH="$L/.lake/landrunbin:$T/nanoda_lib/target/release:$PATH" \
  COMPARATOR_LEAN4EXPORT="$T/lean4export-rc3/.lake/build/bin/lean4export" \
  COMPARATOR_NANODA="$T/nanoda_lib/target/release/nanoda_bin" \
    lake env "$T/comparator/.lake/build/bin/comparator" "$CFG" > "$LOG" 2>&1
  rc=$?
  END=$(date +%s)
  echo "$CFG ($N theorems): EXIT $rc, $((END - START)) s, $(date '+%Y-%m-%d %H:%M')" | tee -a "$L/comparator_runs.txt"
  [ $rc -ne 0 ] && rc_all=$rc
done
exit $rc_all
