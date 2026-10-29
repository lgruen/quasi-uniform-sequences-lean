/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4S6Defs

@[expose] public section

/-!
# Statements: stage V10_4ca2 (paper V4, stage V10-4)

`thm:block`(c), improved `s = 6` design (`blk6dF`): kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at `P = 6367`, `A = 14`, below the option 2 of the first coordinate (11 parts of `11^4` leaves).
PROVED (`GeoSeq/V10_4S6ca2.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_4ca2`
(definitions in `GeoSeq/V10_4S6Defs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-4). Configuration:
`comparatorGeoSeqV10_4ca2.json`.
-/

namespace GeoSeq

section G0

theorem blk6d_chk2_0 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (0, 0)) = true := by
  sorry

theorem blk6d_chk2_1 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (256, 6541134331398)) = true := by
  sorry

theorem blk6d_chk2_2 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (256, 5441841135871)) = true := by
  sorry

theorem blk6d_chk2_3 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (256, 1043626787068)) = true := by
  sorry

theorem blk6d_chk2_4 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (256, 1043576258305)) = true := by
  sorry

theorem blk6d_chk2_5 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (256, 1043677052928)) = true := by
  sorry

theorem blk6d_chk2_6 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (512, -6541134331398)) = true := by
  sorry

theorem blk6d_chk2_7 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (512, -5441841135871)) = true := by
  sorry

theorem blk6d_chk2_8 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (512, -1043626787068)) = true := by
  sorry

theorem blk6d_chk2_9 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (512, -1043576258305)) = true := by
  sorry

theorem blk6d_chk2_10 :
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + (1024, -14250718396914) + (512, -1043677052928)) = true := by
  sorry

end G0

end GeoSeq
