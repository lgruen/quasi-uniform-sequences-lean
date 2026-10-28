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
# GeoSeq stage V9-9: kernel evaluations for `thm:block`(c), `s = 5`, primes 89, 97, 101

Each theorem evaluates the checker `caCheck` (all `9^5 = 59049` steps and capped carry depths) by kernel reduction
(`decide +kernel`, no `native_decide`) (beyond the primes needed by `blk5_block`, which uses the written argument from `p = 84` on); soundness is `caCheck_sound` (`V99Gen`), used in `blk5_LB_chk`.
-/

namespace GeoSeq

set_option maxHeartbeats 0

/-- `LB(F) ≥ 1 - 17/89` for `thm:block`(c), `s = 5`, at `p = 89` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk89 : caCheck 5 blk5Opts blk5St0 89 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/97` for `thm:block`(c), `s = 5`, at `p = 97` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk97 : caCheck 5 blk5Opts blk5St0 97 16 = true := by decide +kernel

/-- `LB(F) ≥ 1 - 17/101` for `thm:block`(c), `s = 5`, at `p = 101` (kernel evaluation of the one-digit relaxation
checker; `tab:block`, c.a. column). -/
theorem blk5_chk101 : caCheck 5 blk5Opts blk5St0 101 16 = true := by decide +kernel

end GeoSeq
