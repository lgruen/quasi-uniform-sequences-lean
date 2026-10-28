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
# Statements: stage V99ca5d (paper V4)

`thm:block`(c), `s = 5`, computer-assisted: kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 71, 73, 79, 83.
PROVED (`GeoSeq/V99Ca5d.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca5d`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca5d.json`.
-/

namespace GeoSeq

section G0

/-- `LB(F) ≥ 1 - 17/71` for `thm:block`(c), `s = 5`, at `p = 71` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk71 : caCheck 5 blk5Opts blk5St0 71 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/73` for `thm:block`(c), `s = 5`, at `p = 73` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk73 : caCheck 5 blk5Opts blk5St0 73 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/79` for `thm:block`(c), `s = 5`, at `p = 79` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk79 : caCheck 5 blk5Opts blk5St0 79 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/83` for `thm:block`(c), `s = 5`, at `p = 83` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk83 : caCheck 5 blk5Opts blk5St0 83 16 = true := by
  sorry

end G0

end GeoSeq
