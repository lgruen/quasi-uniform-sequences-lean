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
# Statements: stage V99ca5e (paper V4)

`thm:block`(c), `s = 5`, computer-assisted: kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 89, 97, 101.
PROVED (`GeoSeq/V99Ca5e.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca5e`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca5e.json`.
-/

namespace GeoSeq

section G0

/-- `LB(F) ≥ 1 - 17/89` for `thm:block`(c), `s = 5`, at `p = 89` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk89 : caCheck 5 blk5Opts blk5St0 89 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/97` for `thm:block`(c), `s = 5`, at `p = 97` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk97 : caCheck 5 blk5Opts blk5St0 97 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/101` for `thm:block`(c), `s = 5`, at `p = 101` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk101 : caCheck 5 blk5Opts blk5St0 101 16 = true := by
  sorry

end G0

end GeoSeq
