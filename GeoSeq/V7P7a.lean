/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7P7Data

@[expose] public section

/-!
# GeoSeq stage V7: the finite check of `thm:p7`, the steps `(1, 1, 1)` and `(1, 1, -1)`

Kernel evaluation (`decide +kernel`) of the checker `p7chk` (`GeoSeq/V7P7Data.lean`) on the steps `(1, 1, 1)` and `(1, 1, -1)`.
-/

namespace GeoSeq

/-- `thm:p7`, step `(1, 1, 1)`: no vanishing combination (`7^6` combinations). -/
theorem p7chk_111 : p7chk 1 1 1 = true := by decide +kernel

/-- `thm:p7`, step `(1, 1, -1)`: no vanishing combination (`7^6` combinations). -/
theorem p7chk_116 : p7chk 1 1 6 = true := by decide +kernel

end GeoSeq
