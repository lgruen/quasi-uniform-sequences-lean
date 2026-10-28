/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Faure2
public import GeoSeq.WFSep
public import GeoSeq.Prefix

@[expose] public section

/-!
# GeoSeq stage S3/S4: `lem:WFlaw` and `thm:WF`

The brick walls `W^±` over a general field `F` of characteristic `≠ 2` (`ρ` any series with
`ρ(0) = 1`, `ρ² = 1 + a x`, `a ≠ 0`), then over `𝔽_p` with `ρ = rhoWF p a`:

* `sq_of_rec`, `rhoWF_sq`: the recursion of `sqrtCoeff` gives `ρ² = 1 + a x`.
* `wf_root`: `z_c² - z_c = (a/4) x` (`eq:roots` for the Faure frame `w = z² - z`, scale `θ = a/4`).
* `wf_O1`, `wf_X10`: `lem:WFlaw` via `law` + `faure_inv` + `gform`: `𝒟[1][1] = 1 - 2 z_1 k_1 = 0`,
  and `E = 2 z_0 k_0/(1-x)` satisfies `E (1 + a x) = -(a/2) x`, so `[x^l] E = ½(-a)^l` for `l ≥ 1`.
* **`WF_law_O1`, `WF_law_X10`** (`lem:WFlaw`, coordinate `1`), **`WF_sep`** (`thm:WF`), **`WF_allN`**
  (`cor:WF`, separation along all `N`).
-/

namespace GeoSeq

open Finset PowerSeries

section General

variable {F : Type*} [Field F]

/-- A series whose coefficients satisfy the recursion of `sqrtCoeff` squares to `1 + a x`. -/
theorem sq_of_rec (h2 : (2 : F) ≠ 0) (a : F) (f : ℕ → F) (h0 : f 0 = 1)
    (hs : ∀ n, f (n + 1) =
      ((if n = 0 then a else 0) - ∑ i : Fin n, f (i + 1) * f (n - i)) * (2 : F)⁻¹) :
    (PowerSeries.mk f) ^ 2 = 1 + C a * X := by
  ext n
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk f) * coeff j (PowerSeries.mk f))]
  simp only [coeff_mk, map_add, coeff_one, coeff_C_mul, coeff_X]
  rcases n with _ | n
  · simp [h0]
  · rw [Nat.succ_eq_add_one, Finset.sum_range_succ', Finset.sum_range_succ]
    have hS : ∑ i ∈ range n, f (i + 1) * f (n + 1 - (i + 1)) = ∑ i : Fin n, f (i + 1) * f (n - i) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => f (i + 1) * f (n + 1 - (i + 1))) n]
      refine sum_congr rfl fun i _ => ?_
      congr 2
      omega
    rw [hS, Nat.sub_zero, Nat.sub_self, h0, hs n]
    have h22 : (2 : F) * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, Fin.sum_univ_zero, sub_zero]
      norm_num
      linear_combination a * h22
    · simp only [hn, ite_false, show n + 1 ≠ 0 by omega, show n + 1 ≠ 1 by omega, zero_sub]
      linear_combination (-(∑ i : Fin n, f (i + 1) * f (n - i))) * h22

lemma wf_C2 (h2 : (2 : F) ≠ 0) : C (2 : F) * C (2 : F)⁻¹ = (1 : PowerSeries F) := by
  rw [← map_mul, mul_inv_cancel₀ h2, map_one]

lemma wf_two : (C (2 : F) : PowerSeries F) = 2 := map_ofNat _ 2

/-- `eq:roots` for `W^±`: `z_c² - z_c = (a/4) x`. -/
theorem wf_root (h2 : (2 : F) ≠ 0) (a : F) (ρ : PowerSeries F) (hρ2 : ρ ^ 2 = 1 + C a * X) (c : Fin 2) :
    Polynomial.aeval (wfZ ρ c) (Polynomial.X ^ 2 - Polynomial.X : Polynomial F) =
      C ((2 : F)⁻¹ * (2 : F)⁻¹ * a) * X := by
  have hC : 2 * C (2 : F)⁻¹ = (1 : PowerSeries F) := by rw [← wf_two, wf_C2 h2]
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_mul]
  fin_cases c
  · show (C (2 : F)⁻¹ * (1 - ρ)) ^ 2 - C (2 : F)⁻¹ * (1 - ρ) = _
    linear_combination (C (2 : F)⁻¹) ^ 2 * hρ2 + ((1 - ρ) * C (2 : F)⁻¹) * hC
  · show (C (2 : F)⁻¹ * (1 + ρ)) ^ 2 - C (2 : F)⁻¹ * (1 + ρ) = _
    linear_combination (C (2 : F)⁻¹) ^ 2 * hρ2 + ((1 + ρ) * C (2 : F)⁻¹) * hC

/-- `E (1 + a x) = -(a h) x` ⟹ `[x^l] E = h (-a)^l` for `l ≥ 1` (the coefficients of `-(a h) x/(1 + a x)`). -/
theorem coeff_geom (E : PowerSeries F) (a h : F) (hE : E * (1 + C a * X) = -(C a * C h * X)) :
    ∀ l, 1 ≤ l → coeff l E = h * (-a) ^ l := by
  have key : ∀ n, coeff (n + 1) E + coeff n E * a = if n = 0 then -(a * h) else 0 := by
    intro n
    have := congrArg (coeff (n + 1)) hE
    rw [mul_add, mul_one, map_add, ← mul_assoc, coeff_succ_mul_X, coeff_mul_C,
      show -(C a * C h * X) = -(C (a * h) * X : PowerSeries F) by rw [map_mul], map_neg,
      coeff_succ_mul_X, coeff_C] at this
    rw [this]
    split_ifs <;> simp
  have h0 : coeff 0 E = 0 := by
    have := congrArg (coeff 0) hE
    rw [mul_add, mul_one, map_add, ← mul_assoc, coeff_zero_mul_X, add_zero, map_neg,
      coeff_zero_mul_X, neg_zero] at this
    exact this
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    have := key 0
    rw [h0, zero_mul, add_zero, zero_add] at this
    simp only [↓reduceIte] at this
    rw [this, pow_one]; ring
  | succ n hn ih =>
    have := key n
    simp only [show ¬ (n = 0) by omega, ite_false] at this
    rw [ih] at this
    rw [pow_succ, eq_neg_of_add_eq_zero_left this]; ring

/-- **`lem:WFlaw`** over `F` (both coordinate-1 responses): `O_1^{(l)} = 0` and
`X_{1←0}^{(l)} = ½ (-a)^l` for every level `K` and `1 ≤ l ≤ K`. -/
theorem wf_law [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (a : F) (ρ : PowerSeries F)
    (ha : a ≠ 0) (hρ0 : constantCoeff ρ = 1) (hρ2 : ρ ^ 2 = 1 + C a * X)
    (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    IsCarryEntry (ssGen (wfG ρ) (wfZ ρ)) K 0 l 1 1 0 ∧
      IsCarryEntry (ssGen (wfG ρ) (wfZ ρ)) K 0 l 1 0 ((2 : F)⁻¹ * (-a) ^ l) := by
  set A : PowerSeries F := ((1 - X) * (1 + ρ))⁻¹ with hAdef
  set g0 : PowerSeries F := C (2 : F) * ρ * A with hg0
  set g1 : PowerSeries F := (1 + ρ) * ρ⁻¹ with hg1
  set z0 : PowerSeries F := C (2 : F)⁻¹ * (1 - ρ) with hz0
  set z1 : PowerSeries F := C (2 : F)⁻¹ * (1 + ρ) with hz1
  have hg : wfG ρ = ![g0, g1] := by
    funext c; fin_cases c <;> rfl
  have hz : wfZ ρ = ![z0, z1] := by
    funext c; fin_cases c <;> rfl
  have hC := wf_C2 h2
  have hcc1X : constantCoeff ((1 - X) * (1 + ρ) : PowerSeries F) = 2 := by
    rw [map_mul, map_sub, map_add, map_one, constantCoeff_X, hρ0, sub_zero, one_mul,
      one_add_one_eq_two]
  have hA : (1 - X) * (1 + ρ) * A = 1 := PowerSeries.mul_inv_cancel _ (by rw [hcc1X]; exact h2)
  have hri : ρ * ρ⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hρ0]; exact one_ne_zero)
  have hccg0 : constantCoeff g0 = 1 := by
    rw [hg0, hAdef, map_mul, map_mul, constantCoeff_inv, hcc1X, constantCoeff_C, hρ0, mul_one,
      mul_inv_cancel₀ h2]
  have hccg1 : constantCoeff g1 = 2 := by
    rw [hg1, map_mul, constantCoeff_inv, map_add, map_one, hρ0, inv_one, mul_one,
      one_add_one_eq_two]
  have hdiff : z1 - z0 = ρ := by
    rw [hz0, hz1]
    have : 2 * C (2 : F)⁻¹ = (1 : PowerSeries F) := by rw [← wf_two, hC]
    linear_combination ρ * this
  set k0 : PowerSeries F := (ρ * g0)⁻¹ with hk0def
  set k1 : PowerSeries F := (ρ * g1)⁻¹ with hk1def
  have hk0 : k0 * (ρ * g0) = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [map_mul, hρ0, hccg0, one_mul]; exact one_ne_zero)
  have hk1 : k1 * (ρ * g1) = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [map_mul, hρ0, hccg1, one_mul]; exact h2)
  have hMG : frameM ![g0, g1] ![z0, z1] * faureG z0 z1 k0 k1 = 1 :=
    faure_inv z0 z1 g0 g1 k0 k1 (by rw [hdiff]; exact hk0) (by rw [hdiff]; exact hk1)
  have hdeg : (Polynomial.X ^ 2 - Polynomial.X : Polynomial F).natDegree ≤ 2 :=
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hθ : (2 : F)⁻¹ * (2 : F)⁻¹ * a * (2 * 2 * a⁻¹) = 1 := by field_simp
  have hroot : ∀ c, Polynomial.aeval (![z0, z1] c) (Polynomial.X ^ 2 - Polynomial.X : Polynomial F) =
      C ((2 : F)⁻¹ * (2 : F)⁻¹ * a) * X := by
    intro c; rw [← hz]; exact wf_root h2 a ρ hρ2 c
  have hz0c : constantCoeff z0 = 0 := by
    rw [hz0, map_mul, map_sub, map_one, hρ0, sub_self, mul_zero]
  have hsum : z0 + z1 = 1 := by
    rw [hz0, hz1]
    have : 2 * C (2 : F)⁻¹ = (1 : PowerSeries F) := by rw [← wf_two, hC]
    linear_combination this
  have hgf := gform z0 z1 g0 g1 k0 k1 hz0c hsum l
  have hlaw := fun c c' => law ![g0, g1] ![z0, z1] _ hdeg _ _ hθ hroot _ hMG K 0 l hl hlK c c'
  rw [hg, hz]
  constructor
  · have h11 := hlaw 1 1
    have hv : lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 = 0 := by
      rw [hgf.2.2.2, hccg1]
      have : 1 - C (2 : F) * z1 * k1 = 0 := by
        rw [hz1, hg1] at *
        linear_combination (-((1 + ρ) * k1)) * hC - hk1 + (k1 * (1 + ρ)) * hri
      rw [this, zero_mul, map_zero]
    rwa [hv] at h11
  · have h10 := hlaw 1 0
    have hv : lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 = (2 : F)⁻¹ * (-a) ^ l := by
      rw [hgf.2.2.1, hccg1]
      have e1 : k0 * (C (2 : F) * ρ ^ 2) = (1 - X) * (1 + ρ) := by
        rw [hg0] at hk0
        linear_combination ((1 - X) * (1 + ρ)) * hk0 - (k0 * C (2 : F) * ρ ^ 2) * hA
      have e2 := mk_one_mul_one_sub_eq_one F
      refine coeff_geom _ a (2 : F)⁻¹ ?_ l hl
      rw [hz0]
      linear_combination (-(C (2 : F) * C (2 : F)⁻¹ * (1 - ρ) * k0 * PowerSeries.mk 1) -
          C (2 : F)⁻¹) * hρ2 + (C (2 : F)⁻¹ * (1 - ρ) * PowerSeries.mk 1) * e1 +
        (C (2 : F)⁻¹ * (1 - ρ) * (1 + ρ)) * e2
    rwa [hv] at h10

end General

/-! ## The brick walls over `𝔽_p` -/

/-- `ρ = √(1 + a x)` (`rhoWF`, defined by the recursion `sqrtCoeff`) squares to `1 + a x`. -/
theorem rhoWF_sq (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ZMod p) :
    rhoWF p a ^ 2 = 1 + C a * X :=
  sq_of_rec (two_ne_zero_zmod p hp) a (sqrtCoeff p a) (sqrtCoeff_zero p a)
    (fun n => by rw [sqrtCoeff])

lemma wf_a_ne (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a = 1 ∨ a = -1) : a ≠ 0 := by
  rcases ha with rfl | rfl
  · exact f_one_ne
  · exact f_neg_one_ne

/-- **`lem:WFlaw`** (own response of coordinate `1`): for `W^±`, every level `K` and carry length
`1 ≤ l ≤ K`, `O_1^{(l)} = D(l)[1][1] = 0`. -/
theorem WF_law_O1 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    IsCarryEntry (WFgen p a) K 0 l 1 1 0 :=
  (wf_law (two_ne_zero_zmod p hp) a (rhoWF p a) (wf_a_ne p a ha) (rhoWF_const p a)
    (rhoWF_sq p hp a) K l hl hlK).1

/-- **`lem:WFlaw`** (cross response into coordinate `1`): for `W^±`, every level `K` and carry
length `1 ≤ l ≤ K`, `X_{1←0}^{(l)} = D(l)[1][0] = ½ (∓1)^l` (`= ½ (-a)^l`). -/
theorem WF_law_X10 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    IsCarryEntry (WFgen p a) K 0 l 1 0 ((2 : ZMod p)⁻¹ * (-a) ^ l) :=
  (wf_law (two_ne_zero_zmod p hp) a (rhoWF p a) (wf_a_ne p a ha) (rhoWF_const p a)
    (rhoWF_sq p hp a) K l hl hlK).2

/-- **`thm:WF`** (separation): `c(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`. -/
theorem WF_sep (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p)) :=
  WF_sep_of_law p hp a ha (fun K l hl hlK => WF_law_O1 p (by omega) a ha K l hl hlK)
    (fun K l hl hlK => WF_law_X10 p (by omega) a ha K l hl hlK) K hK

/-- **`cor:WF`** (separation along all `N`): `δ(P_{[N]}) ≥ (p-3)/(2p²) · N^{-1/2}` for `N ≥ 2`. -/
theorem WF_allN (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1) :
    SepAllN 2 (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p ^ 2)) := by
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have h := prefix_sep p 2 (by omega) (by norm_num) (seqPoint (zcode p) (WFgen p a))
    (((p : ℝ) - 3) / (2 * p)) (div_nonneg (by linarith) (by positivity))
    (fun K hK => WF_sep p hp a ha K hK)
  have e : ((p : ℝ) - 3) / (2 * p) / p = ((p : ℝ) - 3) / (2 * p ^ 2) := by
    rw [div_div]; ring
  rwa [e] at h

end GeoSeq
