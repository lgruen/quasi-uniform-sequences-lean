/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2

@[expose] public section

/-!
# GeoSeq stage V2: the example `ex:MR101` (non-vacuity of `thm:MR` with a positive bound)

`MR101`: for `s = 3`, `p = 101` and the step factors `(h_1, h_2) = (9, 2)` of the mixed-radix rule, the data
of `ex:MR101` (`γ_1 = 5/2`, `γ_2 = 1/2`, `Q_3^3 = 5/2`, `θ = 2`, the rounding of the rule in its rational
form, the crosses `18, 18, -4`, the windows, `M_1 = 5`, `M_2 = 30`, `Γ = 73`) are checked by `decide +kernel`;
the local roots exist; and `thm:MR` gives, for every selection rule, a digital `(0,3)`-sequence over `𝔽_101`
with `c(P_{3K}) ≥ 28/101` for every `K`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

/-- **`ex:MR101`** (non-vacuity of `thm:MR`, `LB = 28/101 > 0`). For `s = 3`: `γ_1 = 5/2`, `γ_2 = 1/2`,
`Q_3^3 = 5/2`, `θ = 2`; the step factors `(9, 2)` are those of the mixed-radix rule
`h_t = max(1, round(γ_t u))`, `u = (101/Q_3^3)^{1/3}`, in the rational form
`(h_t - 1/2)^3 Q_3^3 ≤ γ_t^3 p < (h_t + 1/2)^3 Q_3^3`; the upper crosses are `κ_{0←1} = 18`, `κ_{0←2} = 18`,
`κ_{1←2} = -4`; column `1`: `B_{0←1} = 18`, `M_1 = 5`; column `2`: `B_{0←2} = 18`, `B_{1←2} = 10`, `M_2 = 30`;
`Γ = 73`. The local roots of the Faure frame exist, and for every choice of them a selection rule exists and
every selection rule gives a digital `(0,3)`-sequence over `𝔽_101` with `c(P_{3K}) ≥ 28/101` for all `K ≥ 1`. -/
theorem MR101 :
    mrGamma 3 1 = 5 / 2 ∧ mrGamma 3 2 = 1 / 2 ∧ mrQss 3 = 5 / 2 ∧ mrTheta 3 101 = 2 ∧
    ((17 / 2 : ℚ) ^ 3 * mrQss 3 ≤ mrGamma 3 1 ^ 3 * 101 ∧
      mrGamma 3 1 ^ 3 * 101 < (19 / 2 : ℚ) ^ 3 * mrQss 3) ∧
    ((3 / 2 : ℚ) ^ 3 * mrQss 3 ≤ mrGamma 3 2 ^ 3 * 101 ∧
      mrGamma 3 2 ^ 3 * 101 < (5 / 2 : ℚ) ^ 3 * mrQss 3) ∧
    mrKapZ 3 mrH101 0 1 = 18 ∧ mrKapZ 3 mrH101 0 2 = 18 ∧ mrKapZ 3 mrH101 1 2 = -4 ∧
    mrBx 3 101 mrH101 0 1 = 18 ∧ mrM 3 101 mrH101 1 = 5 ∧
    mrBx 3 101 mrH101 0 2 = 18 ∧ mrBx 3 101 mrH101 1 2 = 10 ∧ mrM 3 101 mrH101 2 = 30 ∧
    mrCost 3 101 mrH101 = 73 ∧
    (∃ zθ : Fin 3 → PowerSeries (ZMod 101),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 101) = C (mrTheta 3 101) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 101)) ∧
    ∀ zθ : Fin 3 → PowerSeries (ZMod 101),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 101) = C (mrTheta 3 101) * X) →
      (∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 101)) →
      (∃ rule : Fin 3 → ℕ → (ℕ → ZMod 101) → ZMod 101,
        IsSelRule (mrTheta 3 101) (mrLam 3 101 mrH101) zθ (mrWin 3 101 mrH101) rule) ∧
      ∀ rule : Fin 3 → ℕ → (ℕ → ZMod 101) → ZMod 101,
        IsSelRule (mrTheta 3 101) (mrLam 3 101 mrH101) zθ (mrWin 3 101 mrH101) rule →
        IsSeq0 (zcode 101) (ssGen (ruleMult (mrTheta 3 101) (mrLam 3 101 mrH101) zθ rule) zθ) ∧
        ∀ K : ℕ, 1 ≤ K → SepAtLevel 101 3 K
          (seqPoint (zcode 101) (ssGen (ruleMult (mrTheta 3 101) (mrLam 3 101 mrH101) zθ rule) zθ))
          (28 / 101) := by
  have hΓ : mrCost 3 101 mrH101 = 73 := by decide +kernel
  have hh : ∀ t, 1 ≤ t → t ≤ 3 - 1 → 1 ≤ mrH101 t := by
    intro t h1 h2; unfold mrH101; split_ifs <;> omega
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, hΓ,
    faure_roots_exist 3 101 (by norm_num) _, fun zθ hroot hplace => ?_⟩
  obtain ⟨hex, hall⟩ := MR 3 101 le_rfl (by norm_num) mrH101 hh (by rw [hΓ]; norm_num) zθ hroot hplace
  refine ⟨hex, fun rule hrule => ?_⟩
  obtain ⟨hseq, hsep, -⟩ := hall rule hrule
  refine ⟨hseq, fun K hK => ?_⟩
  have := hsep K hK
  rw [hΓ] at this
  convert this using 1
  norm_num

end GeoSeq
