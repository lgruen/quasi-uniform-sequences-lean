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
# GeoSeq stage V9-9: kernel evaluations for `thm:block`(c), `s = 5`, primes 37, 41, 43, 47

Each theorem evaluates the checker `caCheck` (all `9^5 = 59049` steps and capped carry depths) by kernel reduction
(`decide +kernel`, no `native_decide`); soundness is `caCheck_sound` (`V99Gen`), used in `blk5_LB_chk`.
-/

namespace GeoSeq

set_option maxHeartbeats 0

/-- `LB(F) ≥ 1 - 17/37` for `thm:block`(c), `s = 5`, at `p = 37` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk37 : caCheck 5 blk5Opts blk5St0 37 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/41` for `thm:block`(c), `s = 5`, at `p = 41` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk41 : caCheck 5 blk5Opts blk5St0 41 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/43` for `thm:block`(c), `s = 5`, at `p = 43` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk43 : caCheck 5 blk5Opts blk5St0 43 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/47` for `thm:block`(c), `s = 5`, at `p = 47` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk47 : caCheck 5 blk5Opts blk5St0 47 16 = true := by decide +kernel

end GeoSeq
