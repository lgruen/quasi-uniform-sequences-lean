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
# GeoSeq stage V7: the finite check of `thm:p7`, the axis steps and the steps with two moving coordinates (first nonzero entry `+1`)

Kernel evaluation (`decide +kernel`) of the checker `p7chk` (`GeoSeq/V7P7Data.lean`) on the axis steps and the steps with two moving coordinates (first nonzero entry `+1`).
-/

namespace GeoSeq

/-- `thm:p7`, the nine steps with one or two moving coordinates whose first nonzero entry is `+1`. -/
theorem p7chk_small : p7chk 1 1 0 = true ∧ p7chk 1 6 0 = true ∧ p7chk 1 0 1 = true ∧ p7chk 1 0 6 = true ∧
    p7chk 0 1 1 = true ∧ p7chk 0 1 6 = true ∧ p7chk 1 0 0 = true ∧ p7chk 0 1 0 = true ∧
    p7chk 0 0 1 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end GeoSeq
