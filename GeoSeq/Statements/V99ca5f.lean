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
# Statements: stage V99ca5f (paper V4)

`thm:block`(c), `s = 5`, computer-assisted: kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 103, 107, 109.
PROVED (`GeoSeq/V99Ca5f.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca5f`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca5f.json`.
-/

namespace GeoSeq

section G0

/-- `LB(F) ≥ 1 - 17/103` for `thm:block`(c), `s = 5`, at `p = 103` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk103 : caCheck 5 blk5Opts blk5St0 103 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/107` for `thm:block`(c), `s = 5`, at `p = 107` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk107 : caCheck 5 blk5Opts blk5St0 107 16 = true := by
  sorry

/-- `LB(F) ≥ 1 - 17/109` for `thm:block`(c), `s = 5`, at `p = 109` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk109 : caCheck 5 blk5Opts blk5St0 109 16 = true := by
  sorry

end G0

end GeoSeq
