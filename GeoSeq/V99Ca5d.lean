/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99Defs

@[expose] public section

/-!
# GeoSeq stage V9-9: kernel evaluations for `thm:block`(c), `s = 5`, primes 71, 73, 79, 83

Each theorem evaluates the checker `caCheck` (all `9^5 = 59049` steps and capped carry depths) by kernel reduction
(`decide +kernel`, no `native_decide`); soundness is `caCheck_sound` (`V99Gen`), used in `blk5_LB_chk`.
-/

namespace GeoSeq

set_option maxHeartbeats 0

/-- `LB(F) ≥ 1 - 17/71` for `thm:block`(c), `s = 5`, at `p = 71` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk71 : caCheck 5 blk5Opts blk5St0 71 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/73` for `thm:block`(c), `s = 5`, at `p = 73` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk73 : caCheck 5 blk5Opts blk5St0 73 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/79` for `thm:block`(c), `s = 5`, at `p = 79` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk79 : caCheck 5 blk5Opts blk5St0 79 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/83` for `thm:block`(c), `s = 5`, at `p = 83` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk83 : caCheck 5 blk5Opts blk5St0 83 16 = true := by decide +kernel

end GeoSeq
