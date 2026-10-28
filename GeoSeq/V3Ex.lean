/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Lexmin
public import GeoSeq.V3Tour

@[expose] public section

/-!
# GeoSeq stage V3: non-vacuity of `thm:MRall`(b)

`MRall_example`: `p = 67` is a prime above `p_1(3) ≤ 63.18`, the local roots of the Faure frame over `𝔽_67` exist,
and `thm:MRall`(b) gives the mixed-radix rule with `Γ < 67` and, for every choice of the roots, a selection
rule and, for every selection rule, a digital `(0,3)`-sequence over `𝔽_67` with `c(P_{3K}) ≥ (67 - Γ)/67 > 0`.
-/

namespace GeoSeq

open PowerSeries

/-- **Non-vacuity of `thm:MRall`(b)** at `s = 3`, `p = 67`. -/
theorem MRall_example :
    mrP1 3 < 67 ∧ mrCost 3 67 (mrRuleH 3 67) < 67 ∧
    (∃ zθ : Fin 3 → PowerSeries (ZMod 67),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 67) = C (mrTheta 3 67) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 67)) ∧
    ∀ zθ : Fin 3 → PowerSeries (ZMod 67),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 67) = C (mrTheta 3 67) * X) →
      (∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 67)) →
      (∃ rule : Fin 3 → ℕ → (ℕ → ZMod 67) → ZMod 67,
        IsSelRule (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ (mrWin 3 67 (mrRuleH 3 67)) rule) ∧
      ∀ rule : Fin 3 → ℕ → (ℕ → ZMod 67) → ZMod 67,
        IsSelRule (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ (mrWin 3 67 (mrRuleH 3 67)) rule →
        IsSeq0 (zcode 67) (ssGen (ruleMult (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ rule) zθ) ∧
        ∀ K : ℕ, 1 ≤ K → SepAtLevel 67 3 K
          (seqPoint (zcode 67) (ssGen (ruleMult (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ rule) zθ))
          (((67 : ℝ) - mrCost 3 67 (mrRuleH 3 67)) / 67) := by
  have hP1 : mrP1 3 < 67 := by
    have := tabP1_s3.2.2.1
    have h : (((6318 / 100 : ℚ)) : ℝ) < 67 := by norm_num
    exact lt_of_le_of_lt this h
  have hb := MRall_b 3 67 le_rfl (by exact_mod_cast hP1) (by norm_num)
  refine ⟨hP1, hb.1, faure_roots_exist 3 67 (by norm_num) _, fun zθ hroot hplace => ?_⟩
  obtain ⟨hex, hall⟩ := hb.2 zθ hroot hplace
  refine ⟨hex, fun rule hrule => ?_⟩
  obtain ⟨hseq, hsep, -⟩ := hall rule hrule
  exact ⟨hseq, fun K hK => by exact_mod_cast hsep K hK⟩

end GeoSeq
