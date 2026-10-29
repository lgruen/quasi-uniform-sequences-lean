/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Blk
public import GeoSeq.V99Blk5Main

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 3b): `thm:block`(c), `s = 5`, equality, unconditional

`blk5_LB_eq`: `LB(F) = 1 - 17/p` at every prime `p ≥ 19`, from the unconditional lower bound `blk5_LB_ca` (whose
closure contains the 16 kernel evaluations `blk5_chk19` … `blk5_chk83`) and the axis step `blk5_LB_attained`. Checked
by `lake build` only (as `blk5_block` in stage V9-9: a Comparator run over the 16 evaluations exceeds the 10-minute
command limit); the Comparator compares `blk5_LB_eq_of` and the evaluations separately.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **`thm:block`(c), `s = 5`, equality** `LB(F) = 1 - 17/p` at every prime `p ≥ 19`. -/
theorem blk5_LB_eq (hp : 19 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p := by
  refine ⟨fun e l h => ?_, blk5_LB_attained (by omega) K hK⟩
  by_cases h84 : 84 ≤ p
  · exact blk5_LB_proof h84 K e l h
  · exact blk5_LB_ca hp (by omega) K e l h

end GeoSeq
