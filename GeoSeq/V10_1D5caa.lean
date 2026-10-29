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
# GeoSeq stage V10-1: `thm:block`(c), `s = 5`, smaller diagonal — kernel evaluations at the primes 23 29 31 37

One `decide +kernel` evaluation of the checker for `blk5dF` (`A = 7`) per prime (no `native_decide`).
-/

namespace GeoSeq

theorem blk5d_chk23 : caCheck 5 blk5dOpts blk5St0 23 7 = true := by decide +kernel
theorem blk5d_chk29 : caCheck 5 blk5dOpts blk5St0 29 7 = true := by decide +kernel
theorem blk5d_chk31 : caCheck 5 blk5dOpts blk5St0 31 7 = true := by decide +kernel
theorem blk5d_chk37 : caCheck 5 blk5dOpts blk5St0 37 7 = true := by decide +kernel

end GeoSeq
