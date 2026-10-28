/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99CovDefs

@[expose] public section

/-!
# Statements: stage V99ca5a (paper V4)

`thm:block`(c), `s = 5`, computer-assisted: kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 19, 23, 29, 31.
PROVED (`GeoSeq/V99Ca5a.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca5a`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca5a.json`.
-/

namespace GeoSeq

section G0

/-- `LB(F) ≥ 1 - 17/19` for `thm:block`(c), `s = 5`, at `p = 19` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk19 : caCheck 5 blk5Opts blk5St0 19 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/23` for `thm:block`(c), `s = 5`, at `p = 23` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk23 : caCheck 5 blk5Opts blk5St0 23 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/29` for `thm:block`(c), `s = 5`, at `p = 29` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk29 : caCheck 5 blk5Opts blk5St0 29 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/31` for `thm:block`(c), `s = 5`, at `p = 31` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk31 : caCheck 5 blk5Opts blk5St0 31 16 = true := by
  sorry

end G0

end GeoSeq
