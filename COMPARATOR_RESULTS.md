# Comparator results

[Comparator](https://github.com/leanprover/comparator) (with `lean4export` at the toolchain's tag and the NanoDa
kernel; on macOS `landrun` replaced by `scripts/fake-landrun.sh`, i.e. without sandbox) was run on this tree after a
complete `lake build` (2026-10-29; Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`; 10-core, 32 GB laptop), one
configuration at a time, each in the foreground with a wall-clock limit. For every accepted configuration the log ends
with `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`.
Every configuration permits exactly `propext`, `Quot.sound`, `Classical.choice`.

## Accepted on this tree: all 79 configurations

| configuration | theorems | result | wall time |
|---|---|---|---|
| `comparatorHeadlineSeqV4.json` | 4 | both kernels accept, EXIT 0 | 52 s |
| `comparatorGeoSeqV10_1.json` | 55 | both kernels accept, EXIT 0 | 148 s |
| `comparatorGeoSeqV10_1ca5_p23.json` | 1 | both kernels accept, EXIT 0 | 98 s |
| `comparatorGeoSeqV10_1ca5_p29.json` | 1 | both kernels accept, EXIT 0 | 84 s |
| `comparatorGeoSeqV10_1ca5_p31.json` | 1 | both kernels accept, EXIT 0 | 84 s |
| `comparatorGeoSeqV10_1ca5_p37.json` | 1 | both kernels accept, EXIT 0 | 83 s |
| `comparatorGeoSeqV10_1ca5_p41.json` | 1 | both kernels accept, EXIT 0 | 83 s |
| `comparatorGeoSeqV10_1ca5_p43.json` | 1 | both kernels accept, EXIT 0 | 84 s |
| `comparatorGeoSeqV10_1ca5_p47.json` | 1 | both kernels accept, EXIT 0 | 83 s |
| `comparatorGeoSeqV10_1ca5_p53.json` | 1 | both kernels accept, EXIT 0 | 83 s |
| `comparatorGeoSeqV10_1ca5_p59.json` | 1 | both kernels accept, EXIT 0 | 83 s |
| `comparatorGeoSeqV10_1ca5_p61.json` | 1 | both kernels accept, EXIT 0 | 84 s |
| `comparatorGeoSeqV10_2.json` | 41 | both kernels accept, EXIT 0 | 40 s |
| `comparatorGeoSeqV10_3.json` | 63 | both kernels accept, EXIT 0 | 167 s |
| `comparatorGeoSeqV10_3x.json` | 41 | both kernels accept, EXIT 0 | 214 s |
| `comparatorGeoSeqV10_4.json` | 37 | both kernels accept, EXIT 0 | 61 s |
| `comparatorGeoSeqV10_4ca0.json` | 11 | both kernels accept, EXIT 0 | 139 s |
| `comparatorGeoSeqV10_4ca1.json` | 11 | both kernels accept, EXIT 0 | 159 s |
| `comparatorGeoSeqV10_4ca10.json` | 11 | both kernels accept, EXIT 0 | 156 s |
| `comparatorGeoSeqV10_4ca2.json` | 11 | both kernels accept, EXIT 0 | 158 s |
| `comparatorGeoSeqV10_4ca3.json` | 11 | both kernels accept, EXIT 0 | 158 s |
| `comparatorGeoSeqV10_4ca4.json` | 11 | both kernels accept, EXIT 0 | 158 s |
| `comparatorGeoSeqV10_4ca5.json` | 11 | both kernels accept, EXIT 0 | 158 s |
| `comparatorGeoSeqV10_4ca6.json` | 11 | both kernels accept, EXIT 0 | 156 s |
| `comparatorGeoSeqV10_4ca7.json` | 11 | both kernels accept, EXIT 0 | 156 s |
| `comparatorGeoSeqV10_4ca8.json` | 11 | both kernels accept, EXIT 0 | 156 s |
| `comparatorGeoSeqV10_4ca9.json` | 11 | both kernels accept, EXIT 0 | 158 s |
| `comparatorGeoSeqV9.json` | 55 | both kernels accept, EXIT 0 | 57 s |
| `comparatorGeoSeqV99cov.json` | 2 | both kernels accept, EXIT 0 | 138 s |
| `comparatorGeoSeqV93.json` | 36 | both kernels accept, EXIT 0 | 36 s |
| `comparatorGeoSeqV94.json` | 34 | both kernels accept, EXIT 0 | 42 s |
| `comparatorGeoSeqV95.json` | 46 | both kernels accept, EXIT 0 | 35 s |
| `comparatorGeoSeqV96.json` | 34 | both kernels accept, EXIT 0 | 39 s |
| `comparatorGeoSeqV97.json` | 17 | both kernels accept, EXIT 0 | 37 s |
| `comparatorGeoSeqV98.json` | 41 | both kernels accept, EXIT 0 | 48 s |
| `comparatorGeoSeqV99.json` | 22 | both kernels accept, EXIT 0 | 76 s |
| `comparatorGeoSeqV99ca.json` | 2 | both kernels accept, EXIT 0 | 38 s |
| `comparatorGeoSeqV99ca5_p101.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p103.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p107.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p109.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p19.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p23.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p29.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p31.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p37.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p41.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p43.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p47.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p53.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p59.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p61.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p67.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p71.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p73.json` | 1 | both kernels accept, EXIT 0 | 78 s |
| `comparatorGeoSeqV99ca5_p79.json` | 1 | both kernels accept, EXIT 0 | 78 s |
| `comparatorGeoSeqV99ca5_p83.json` | 1 | both kernels accept, EXIT 0 | 77 s |
| `comparatorGeoSeqV99ca5_p89.json` | 1 | both kernels accept, EXIT 0 | 78 s |
| `comparatorGeoSeqV99ca5_p97.json` | 1 | both kernels accept, EXIT 0 | 78 s |
| `comparatorGeoSeqV0.json` | 6 | both kernels accept, EXIT 0 | 42 s |
| `comparatorGeoSeqV1.json` | 26 | both kernels accept, EXIT 0 | 38 s |
| `comparatorGeoSeqS11.json` | 1 | both kernels accept, EXIT 0 | 15 s |
| `comparatorGeoSeqS10.json` | 23 | both kernels accept, EXIT 0 | 32 s |
| `comparatorGeoSeqV2.json` | 30 | both kernels accept, EXIT 0 | 41 s |
| `comparatorGeoSeqV3.json` | 33 | both kernels accept, EXIT 0 | 59 s |
| `comparatorGeoSeqV4s4.json` | 2 | both kernels accept, EXIT 0 | 55 s |
| `comparatorGeoSeqV4s5.json` | 2 | both kernels accept, EXIT 0 | 250 s |
| `comparatorGeoSeqV4.json` | 15 | both kernels accept, EXIT 0 | 71 s |
| `comparatorGeoSeqV5.json` | 32 | both kernels accept, EXIT 0 | 45 s |
| `comparatorGeoSeqV6.json` | 16 | both kernels accept, EXIT 0 | 44 s |
| `comparatorGeoSeq.json` | 140 | both kernels accept, EXIT 0 | 139 s |
| `comparatorGeoSeqV7.json` | 23 | both kernels accept, EXIT 0 | 119 s |
| `comparatorGeoSeqV7d45.json` | 3 | both kernels accept, EXIT 0 | 302 s |
| `comparatorGeoSeqK4.json` | 34 | both kernels accept, EXIT 0 | 275 s |
| `comparatorGeoSeqS3core.json` | 16 | both kernels accept, EXIT 0 | 99 s |
| `comparatorGeoSeqS4core.json` | 15 | both kernels accept, EXIT 0 | 62 s |
| `comparatorGeoSeqS3.json` | 24 | both kernels accept, EXIT 0 | 841 s |
| `comparatorGeoSeqS4.json` | 27 | both kernels accept, EXIT 0 | 757 s |
| `comparatorGeoSeqV7full.json` | 3 | both kernels accept, EXIT 0 | 1194 s |

Total wall time of the runs on this tree 9967 s. This covers the 58 configurations of the results new in version 1
(679 theorems: 32 from the first stages, `comparatorGeoSeqV9*.json`, 26 added later, `comparatorGeoSeqV10_*.json`),
the Palomar entry `comparatorHeadlineSeqV4.json`, and the 20 configurations of the results kept from the previous
version. (`comparatorGeoSeqS3core.json` and `comparatorGeoSeqS4core.json` are subsets of `comparatorGeoSeqS3.json` and
`comparatorGeoSeqS4.json`, kept as shorter runs.) One run of `comparatorGeoSeqV7d45.json` was stopped at the wall-clock
limit (150 s left in its batch) and repeated without a shorter limit (accepted, the time above). The Lean files of this
tree were not changed after these runs.

## Build

A complete `lake build` of this tree from the Mathlib cache (the default targets: `Z3Net`, `GeoSeq`, `HeadlineSeqV4`
and every Challenge/Solution root) succeeds. Measured on 2026-10-29: about 63 minutes of wall time for the modules of
the first stages (including one interrupted parallel attempt), built in pieces (`Z3Net` 3.5 min; the heaviest single
modules: `GeoSeq.S3Cert0`, `S3Cert1`, `S3Cert2` about 3.5 min each, `GeoSeq.V99Ca5a`–`f` 2–2.7 min each,
`GeoSeq.S4AutoB`–`D` together 3.6 min), and about 30 minutes for the modules added later, built one heavy module at a
time (`GeoSeq.V10_1D5caa`, `…cab`, `…cac` 145 s, 146 s, 74 s; `GeoSeq.V10_3RowsX` 103 s; `GeoSeq.V10_4S6ca0`–`ca10`
101–104 s each; the rest in one `lake build`, 78 s). A fully parallel build exceeded the memory of the 32 GB machine
(heavy swapping); building the heavy modules first, one at a time, and the rest afterwards avoids this. The build
reports `declaration uses 'sorry'` only for the statement files (`GeoSeq/Statements/*.lean`,
`HeadlineSeqV4/Challenge.lean`), and every `#print axioms` lists a subset of `propext`, `Classical.choice`, `Quot.sound`.
