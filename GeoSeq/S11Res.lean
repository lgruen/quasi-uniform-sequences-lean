/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S11Defs

@[expose] public section

/-!
# GeoSeq stage S11: the residue theorem of the Faure frame (`lem:residue`, `s = 2`)

* `coeff_inv_pow`: `[t^m] (t + δ)^{-e} = δ^e (-δ)^m binom(e-1+m, e-1)` for `δ² = 1`, `e ≥ 1`.
* **`residue2`**: the residue theorem on `ℙ¹` for `V dz / (z^A (z-1)^B)`, `deg V ≤ A + B - 2`:
  `Res_0 + Res_1 = 0`, i.e. `[z^{A-1}] V (z-1)^{-B} + [t^{B-1}] V(1+t) (1+t)^{-A} = 0`. Proved by
  linearity from the binomial identity `binom(N, B-1) = binom(N, A-1-m)`, `N = A+B-2-m` (no residue
  calculus needed).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-- `[t^m] (t + δ)^{-e} = δ^e (-δ)^m binom(e-1+m, e-1)` for `δ · δ = 1`, `e ≥ 1`. -/
lemma coeff_inv_pow (δ : F) (hδ : δ * δ = 1) (e m : ℕ) (he : 1 ≤ e) :
    coeff m (((X + C δ : PS) ^ e)⁻¹) = δ ^ e * (-δ) ^ m * ((e - 1 + m).choose (e - 1) : F) := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  simp only [add_tsub_cancel_right]
  have hS := mk_add_choose_mul_one_sub_pow_eq_one (S := F) (d := d)
  have hR := congrArg (rescale (-δ)) hS
  rw [map_mul, map_pow, map_sub, map_one, rescale_X] at hR
  have hX : (X + C δ : PS) = C δ * (1 - C (-δ) * X) := by
    rw [map_neg, neg_mul, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, ← map_mul, hδ, map_one,
      one_mul, add_comm]
  have hinv : ((X + C δ : PS) ^ (d + 1))⁻¹ =
      C (δ ^ (d + 1)) * rescale (-δ) (mk fun n => ((d + n).choose d : F)) := by
    have hδ0 : δ ≠ 0 := fun h => by simp [h] at hδ
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hδ0])]
    have hc : C (δ ^ (d + 1)) * C (δ ^ (d + 1)) = (1 : PS) := by
      rw [← map_mul, ← mul_pow, hδ, one_pow, map_one]
    rw [hX, mul_pow, ← map_pow]
    linear_combination (C (δ ^ (d + 1)) * C (δ ^ (d + 1))) * hR + hc
  rw [hinv, coeff_C_mul, coeff_rescale, coeff_mk]
  ring

lemma coeff_inv_pow_one (e m : ℕ) (he : 1 ≤ e) :
    coeff m (((X + C 1 : PS) ^ e)⁻¹) = (-1) ^ m * ((e - 1 + m).choose (e - 1) : F) := by
  rw [coeff_inv_pow 1 (one_mul 1) e m he, one_pow, one_mul]

lemma coeff_inv_pow_neg_one (e m : ℕ) (he : 1 ≤ e) :
    coeff m (((X + C (-1) : PS) ^ e)⁻¹) = (-1) ^ e * ((e - 1 + m).choose (e - 1) : F) := by
  rw [coeff_inv_pow (-1) (by ring) e m he, neg_neg, one_pow, mul_one]

lemma constantCoeff_X_add_C_pow_ne (δ : F) (hδ : δ ≠ 0) (e : ℕ) :
    constantCoeff ((X + C δ : PS) ^ e) ≠ 0 := by
  simp [hδ]

/-- A polynomial of degree `< N` is the sum of its monomials. -/
lemma poly_sum_range (V : F[X]) (N : ℕ) (hV : V.natDegree < N) :
    V = ∑ m ∈ range N, Polynomial.C (V.coeff m) * Polynomial.X ^ m := by
  conv_lhs => rw [V.as_sum_range' N hV]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial]

/-- The coefficient functional `V ↦ [t^j] (V(a + t) · h)` is linear in `V`. -/
lemma resFun_sum (a : F) (h : PS) (j N : ℕ) (V : F[X]) (hV : V.natDegree < N) :
    coeff j ((Polynomial.taylor a V : PS) * h) =
      ∑ m ∈ range N, V.coeff m * coeff j ((Polynomial.taylor a (Polynomial.X ^ m) : PS) * h) := by
  conv_lhs => rw [poly_sum_range V N hV]
  rw [map_sum, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.taylor_mul, Polynomial.taylor_C,
    Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, coeff_C_mul]

/-- The binomial core of `residue2`: `V = z^m`, `m ≤ A + B - 2`. -/
lemma residue2_mono (A B m : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hm : m + 2 ≤ A + B) :
    coeff (A - 1) ((Polynomial.taylor (0 : F) (Polynomial.X ^ m) : PS) * ((X + C (-1)) ^ B)⁻¹) +
      coeff (B - 1) ((Polynomial.taylor (1 : F) (Polynomial.X ^ m) : PS) * ((X + C 1) ^ A)⁻¹) = 0 := by
  rw [Polynomial.taylor_X_pow, Polynomial.taylor_X_pow, map_zero, add_zero, Polynomial.coe_pow,
    Polynomial.coe_X, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C,
    map_one, ← map_one (C (R := F))]
  rcases lt_or_ge m A with hmA | hmA
  · -- both terms are binomial coefficients
    have h1 : coeff (A - 1) ((X : PS) ^ m * ((X + C (-1)) ^ B)⁻¹) =
        (-1) ^ B * ((B - 1 + (A - 1 - m)).choose (B - 1) : F) := by
      rw [show A - 1 = (A - 1 - m) + m by omega, coeff_X_pow_mul', ite_eq_left (by omega),
        Nat.add_sub_cancel, coeff_inv_pow_neg_one B _ hB]
    have h2 : coeff (B - 1) ((X + C 1 : PS) ^ m * ((X + C 1) ^ A)⁻¹) =
        (-1) ^ (B - 1) * ((A - m - 1 + (B - 1)).choose (A - m - 1) : F) := by
      have : (X + C 1 : PS) ^ m * ((X + C 1) ^ A)⁻¹ = ((X + C 1) ^ (A - m))⁻¹ := by
        rw [PowerSeries.eq_inv_iff_mul_eq_one (constantCoeff_X_add_C_pow_ne 1 one_ne_zero _),
          mul_assoc, mul_comm _ ((X + C 1 : PS) ^ (A - m)), ← mul_assoc, ← pow_add,
          show m + (A - m) = A by omega]
        exact PowerSeries.mul_inv_cancel _ (constantCoeff_X_add_C_pow_ne 1 one_ne_zero _)
      rw [this, coeff_inv_pow_one (A - m) _ (by omega)]
    rw [h1, h2]
    have hc : (B - 1 + (A - 1 - m)).choose (B - 1) = (A - m - 1 + (B - 1)).choose (A - m - 1) := by
      rw [show A - 1 - m = A - m - 1 by omega, add_comm, Nat.choose_symm_add]
    rw [hc]
    obtain ⟨b, rfl⟩ : ∃ b, B = b + 1 := ⟨B - 1, by omega⟩
    simp only [add_tsub_cancel_right, pow_succ]
    ring
  · -- both terms vanish
    have h1 : coeff (A - 1) ((X : PS) ^ m * ((X + C (-1)) ^ B)⁻¹) = 0 := by
      rw [coeff_X_pow_mul', ite_eq_right (by omega)]
    have h2 : coeff (B - 1) ((X + C 1 : PS) ^ m * ((X + C 1) ^ A)⁻¹) = 0 := by
      have : (X + C 1 : PS) ^ m * ((X + C 1) ^ A)⁻¹ = (X + C 1) ^ (m - A) := by
        rw [show m = (m - A) + A by omega, pow_add, mul_assoc,
          PowerSeries.mul_inv_cancel _ (constantCoeff_X_add_C_pow_ne 1 one_ne_zero _), mul_one,
          show m - A + A - A = m - A by omega]
      rw [this, ← Polynomial.coe_C, ← Polynomial.coe_X, ← Polynomial.coe_add,
        ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow, one_pow, one_mul,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [h1, h2, add_zero]

/-- **The residue theorem of the Faure frame** (`lem:residue`, `s = 2`; the residue theorem on `ℙ¹` for
`V dz / (z^A (z-1)^B)`, holomorphic at `∞` when `deg V ≤ A + B - 2`): `Res_0 + Res_1 = 0`, where
`Res_0 = [z^{A-1}] V(z) (z-1)^{-B}` and `Res_1 = [t^{B-1}] V(1+t) (1+t)^{-A}`. -/
theorem residue2 (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (V : F[X]) (hV : V.natDegree + 2 ≤ A + B) :
    coeff (A - 1) ((Polynomial.taylor (0 : F) V : PS) * ((X + C (-1)) ^ B)⁻¹) +
      coeff (B - 1) ((Polynomial.taylor (1 : F) V : PS) * ((X + C 1) ^ A)⁻¹) = 0 := by
  rw [resFun_sum 0 _ _ (A + B - 1) V (by omega), resFun_sum 1 _ _ (A + B - 1) V (by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [← mul_add, residue2_mono A B m hA hB (by simp at hm; omega), mul_zero]

end GeoSeq
