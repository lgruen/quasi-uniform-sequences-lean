/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Sign

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 9): `thm:block`(c), `s = 5`, smaller free diagonal — the evaluation at `P = 1361`

One kernel evaluation of the checker for `blk5dF` (`A = 7`) at the prime `P = 1361` (`s S² + 2A + 3 = 2662 < 2P`,
`S = 23`), which certifies the sign-class condition (`blk5d_signclass` in `GeoSeq/V10_1Diag5.lean`).
-/

namespace GeoSeq

theorem blk5d_chk1361 : caCheck 5 blk5dOpts blk5St0 1361 7 = true := by decide +kernel

end GeoSeq
