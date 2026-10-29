/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs

@[expose] public section

/-!
# Statements: stage V10_1ca5c (paper V4, stage V10-1)

`thm:block`(c), `s = 5`, design with the smaller free diagonal (`blk5dF`): kernel evaluations (`decide +kernel`) of the one-digit relaxation checker at the primes 59, 61.
PROVED (`GeoSeq/V10_1D5cac.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_1ca5c`
(definitions in `GeoSeq/V10_1Defs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-1). Configuration:
`comparatorGeoSeqV10_1ca5c.json`.
-/

namespace GeoSeq

section G0

theorem blk5d_chk59 : caCheck 5 blk5dOpts blk5St0 59 7 = true := by
  sorry

theorem blk5d_chk61 : caCheck 5 blk5dOpts blk5St0 61 7 = true := by
  sorry

end G0

end GeoSeq
