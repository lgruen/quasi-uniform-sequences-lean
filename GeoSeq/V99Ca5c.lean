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
# GeoSeq stage V9-9: kernel evaluations for `thm:block`(c), `s = 5`, primes 53, 59, 61, 67

Each theorem evaluates the checker `caCheck` (all `9^5 = 59049` steps and capped carry depths) by kernel reduction
(`decide +kernel`, no `native_decide`); soundness is `caCheck_sound` (`V99Gen`), used in `blk5_LB_chk`.
-/

namespace GeoSeq

set_option maxHeartbeats 0

/-- `LB(F) ≥ 1 - 17/53` for `thm:block`(c), `s = 5`, at `p = 53` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk53 : caCheck 5 blk5Opts blk5St0 53 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/59` for `thm:block`(c), `s = 5`, at `p = 59` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk59 : caCheck 5 blk5Opts blk5St0 59 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/61` for `thm:block`(c), `s = 5`, at `p = 61` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk61 : caCheck 5 blk5Opts blk5St0 61 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/67` for `thm:block`(c), `s = 5`, at `p = 67` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk67 : caCheck 5 blk5Opts blk5St0 67 16 = true := by decide +kernel

end GeoSeq
