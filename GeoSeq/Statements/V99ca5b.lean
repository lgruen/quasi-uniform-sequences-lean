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
# Statements: stage V99ca5b (paper V4)

`thm:block`(c), `s = 5`, computer-assisted: kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 37, 41, 43, 47.
PROVED (`GeoSeq/V99Ca5b.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca5b`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca5b.json`.
-/

namespace GeoSeq

section G0

/-- `LB(F) ≥ 1 - 17/37` for `thm:block`(c), `s = 5`, at `p = 37` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk37 : caCheck 5 blk5Opts blk5St0 37 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/41` for `thm:block`(c), `s = 5`, at `p = 41` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk41 : caCheck 5 blk5Opts blk5St0 41 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/43` for `thm:block`(c), `s = 5`, at `p = 43` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk43 : caCheck 5 blk5Opts blk5St0 43 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/47` for `thm:block`(c), `s = 5`, at `p = 47` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk47 : caCheck 5 blk5Opts blk5St0 47 16 = true := by
  sorry

end G0

end GeoSeq
