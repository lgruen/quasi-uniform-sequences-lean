/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Law
public import GeoSeq.Cert
public import GeoSeq.FrameNets

@[expose] public section

/-!
# GeoSeq stage S3: `thm:WF` (separation) from `lem:WFlaw`

`WF_sep_of_law`: the separation half of `thm:WF` follows from the two coordinate-1 statements of
`lem:WFlaw` (`O_1^{(l)} = 0`, `X_{1←0}^{(l)} = ½(∓1)^l`, as in `WF_law_O1`, `WF_law_X10`), by
`cert_one` (`lem:cert`, `j = 1`), the `t = 0` property `WF_net`, the existence of the remaining carry
responses (`carry_exists`; coordinate `0` is arbitrary) and the arithmetic core `WF_LB1`. So
`thm:WF` reduces to the series identities of `lem:WFlaw` (stage S4).
-/

namespace GeoSeq

open Finset

lemma pm_pow {F : Type*} [Field F] (a : F) (ha : a = 1 ∨ a = -1) (n : ℕ) :
    (-a) ^ n = 1 ∨ (-a) ^ n = -1 := by
  rcases ha with rfl | rfl
  · exact neg_one_pow_eq_or F n
  · left; rw [neg_neg, one_pow]

/-- **`thm:WF` (separation) from `lem:WFlaw`**: if the own response of coordinate `1` vanishes and its
cross response is `½(-a)^l` at every level, then `c(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`. -/
theorem WF_sep_of_law (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (hO : ∀ K l : ℕ, 1 ≤ l → l ≤ K → IsCarryEntry (WFgen p a) K 0 l 1 1 0)
    (hX : ∀ K l : ℕ, 1 ≤ l → l ≤ K →
      IsCarryEntry (WFgen p a) K 0 l 1 0 ((2 : ZMod p)⁻¹ * (-a) ^ l))
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p)) := by
  have hnet : BlockNet0 (zcode p) (WFgen p a) (2 * K) 0 := WF_net p hp a ha (2 * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  classical
  let Dr : ℕ → Fin 2 → Fin 2 → ZMod p := fun l c c' =>
    if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists (zcode p) (WFgen p a) K hnet 0 l c c')
    else 0
  have hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry (WFgen p a) K 0 l c c' (Dr l c c') := by
    intro l h1 h2 c c'
    simp only [Dr, And.intro h1 h2, and_self, dite_true]
    exact Classical.choose_spec (carry_exists (zcode p) (WFgen p a) K hnet 0 l c c')
  have hD11 : ∀ l, 1 ≤ l → l ≤ K → Dr l 1 1 = 0 := fun l h1 h2 =>
    carryEntry_unique _ _ _ _ _ _ (hD l h1 h2 1 1) (hO K l h1 h2)
  have hD10 : ∀ l, 1 ≤ l → l ≤ K → Dr l 1 0 = (2 : ZMod p)⁻¹ * (-a) ^ l := fun l h1 h2 =>
    carryEntry_unique _ _ _ _ _ _ (hD l h1 h2 1 0) (hX K l h1 h2)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 3) / (2 * p) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h := cert_one (WFgen p a) K hq hnet Dr hD (((p : ℝ) - 3) / (2 * p)) ?_
  · rwa [min_eq_right hLB1] at h
  rintro e l ⟨he, hne, hl⟩
  have he0 : e 0 = -1 ∨ e 0 = 0 ∨ e 0 = 1 := by have := he 0; omega
  have he1 : e 1 = -1 ∨ e 1 = 0 ∨ e 1 = 1 := by have := he 1; omega
  have hne' : e 0 ≠ 0 ∨ e 1 ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    fin_cases c
    · exact Or.inl hc
    · exact Or.inr hc
  set x : ZMod p := (2 : ZMod p)⁻¹ * (-a) ^ l 0 with hxdef
  have hx : x = (2 : ZMod p)⁻¹ ∨ x = -(2 : ZMod p)⁻¹ := by
    rcases pm_pow a ha (l 0) with h1 | h1
    · left; exact hxdef.trans ((congrArg (fun t => (2 : ZMod p)⁻¹ * t) h1).trans (mul_one _))
    · right; exact hxdef.trans ((congrArg (fun t => (2 : ZMod p)⁻¹ * t) h1).trans (mul_neg_one _))
  have hσ1 : ∑ c', (e c' : ZMod p) * Dr (l c') 1 c' = (e 0 : ZMod p) * x := by
    rw [Fin.sum_univ_two, hD10 (l 0) (hl 0).1 (hl 0).2, hD11 (l 1) (hl 1).1 (hl 1).2, mul_zero,
      add_zero]
  rw [Fin.sum_univ_two, hσ1]
  set σ0 := ∑ c', (e c' : ZMod p) * Dr (l c') 0 c'
  have key := WF_LB1 p hp (e 0) (e 1) he0 he1 hne' x hx σ0
  set g0 := gapNum1 p (e 0) σ0
  set g1 := gapNum1 p (e 1) ((e 0 : ZMod p) * x)
  have keyR : ((p : ℝ) - 3) ^ 2 ≤ 4 * ((g0 : ℝ) ^ 2 + (g1 : ℝ) ^ 2) := by
    have : (((p - 3 : ℕ) : ℝ)) = (p : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [← this]
    exact_mod_cast key
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, div_pow, div_pow, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hp2 : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right keyR hp2]

end GeoSeq
