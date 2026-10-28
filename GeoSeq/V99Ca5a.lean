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
# GeoSeq stage V9-9: kernel evaluations for `thm:block`(c), `s = 5`, primes 19, 23, 29, 31

Each theorem evaluates the checker `caCheck` (all `9^5 = 59049` steps and capped carry depths) by kernel reduction
(`decide +kernel`, no `native_decide`); soundness is `caCheck_sound` (`V99Gen`), used in `blk5_LB_chk`.
-/

namespace GeoSeq

set_option maxHeartbeats 0

/-- `LB(F) ≥ 1 - 17/19` for `thm:block`(c), `s = 5`, at `p = 19` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk19 : caCheck 5 blk5Opts blk5St0 19 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/23` for `thm:block`(c), `s = 5`, at `p = 23` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk23 : caCheck 5 blk5Opts blk5St0 23 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/29` for `thm:block`(c), `s = 5`, at `p = 29` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk29 : caCheck 5 blk5Opts blk5St0 29 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/31` for `thm:block`(c), `s = 5`, at `p = 31` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk31 : caCheck 5 blk5Opts blk5St0 31 16 = true := by decide +kernel

end GeoSeq
