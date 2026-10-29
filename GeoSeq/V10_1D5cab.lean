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
# GeoSeq stage V10-1: `thm:block`(c), `s = 5`, smaller diagonal — kernel evaluations at the primes 41 43 47 53

One `decide +kernel` evaluation of the checker for `blk5dF` (`A = 7`) per prime (no `native_decide`).
-/

namespace GeoSeq

theorem blk5d_chk41 : caCheck 5 blk5dOpts blk5St0 41 7 = true := by decide +kernel
theorem blk5d_chk43 : caCheck 5 blk5dOpts blk5St0 43 7 = true := by decide +kernel
theorem blk5d_chk47 : caCheck 5 blk5dOpts blk5St0 47 7 = true := by decide +kernel
theorem blk5d_chk53 : caCheck 5 blk5dOpts blk5St0 53 7 = true := by decide +kernel

end GeoSeq
