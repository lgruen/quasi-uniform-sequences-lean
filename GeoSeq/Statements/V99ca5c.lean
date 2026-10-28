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
# Statements: stage V99ca5c (paper V4)

`thm:block`(c), `s = 5`, computer-assisted: kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 53, 59, 61, 67.
PROVED (`GeoSeq/V99Ca5c.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca5c`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca5c.json`.
-/

namespace GeoSeq

section G0

/-- `LB(F) ≥ 1 - 17/53` for `thm:block`(c), `s = 5`, at `p = 53` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk53 : caCheck 5 blk5Opts blk5St0 53 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/59` for `thm:block`(c), `s = 5`, at `p = 59` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk59 : caCheck 5 blk5Opts blk5St0 59 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/61` for `thm:block`(c), `s = 5`, at `p = 61` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk61 : caCheck 5 blk5Opts blk5St0 61 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/67` for `thm:block`(c), `s = 5`, at `p = 67` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk67 : caCheck 5 blk5Opts blk5St0 67 16 = true := by
  sorry

end G0

end GeoSeq
