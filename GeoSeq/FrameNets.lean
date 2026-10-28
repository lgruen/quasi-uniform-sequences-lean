/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SSFrame

@[expose] public section

/-!
# GeoSeq stage S1: `t = 0` of the brick walls (`thm:WF`) and of the base-2 sequence (`thm:B2`)

Both are self-similar scrambles of the Faure frame with places `0, 1` (`ss_t0`): the constant
terms and linear coefficients of the multipliers and local roots are computed here.
-/

namespace GeoSeq

open Finset PowerSeries

lemma sqrtCoeff_zero (p : ℕ) (a : ZMod p) : sqrtCoeff p a 0 = 1 := by
  rw [sqrtCoeff]

lemma sqrtCoeff_one (p : ℕ) (a : ZMod p) : sqrtCoeff p a 1 = a * (2 : ZMod p)⁻¹ := by
  rw [sqrtCoeff]; simp

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

lemma rhoWF_const (p : ℕ) (a : ZMod p) : constantCoeff (rhoWF p a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, rhoWF, coeff_mk, sqrtCoeff_zero]

lemma rhoWF_coeff1 (p : ℕ) (a : ZMod p) : coeff 1 (rhoWF p a) = a * (2 : ZMod p)⁻¹ := by
  rw [rhoWF, coeff_mk, sqrtCoeff_one]

/-- Field facts stated for a general field: applied to `ZMod p` they unify with the ring
operations of `ZMod p` at default transparency (instance search alone does not, for variable `p`). -/
lemma f_one_ne {K : Type*} [Field K] : (1 : K) ≠ 0 := one_ne_zero
lemma f_neg_one_ne {K : Type*} [Field K] : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
lemma f_mul_ne {K : Type*} [Field K] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 :=
  mul_ne_zero hx hy
lemma f_neg_ne {K : Type*} [Field K] {x : K} (hx : x ≠ 0) : -x ≠ 0 := neg_ne_zero.mpr hx

/-! ### Constant terms and linear coefficients of `W^±`

The subtraction in `1 - ρ` is elaborated through the field structure of `ZMod p`, which is not
reducibly the ring structure of `ZMod p` for a variable `p`; the rewrites are therefore closed by
explicit intermediate forms. -/

lemma WFz0_const (p : ℕ) [Fact p.Prime] (a : ZMod p) : constantCoeff (WFz p a 0) = 0 := by
  have e : constantCoeff (WFz p a 0) = (2 : ZMod p)⁻¹ * (1 - 1) := by
    show constantCoeff (C (2 : ZMod p)⁻¹ * (1 - rhoWF p a)) = _
    rw [map_mul, map_sub, map_one, rhoWF_const, constantCoeff_C]; rfl
  rw [e, sub_self, mul_zero]
lemma WFz1_const (p : ℕ) [Fact p.Prime] (a : ZMod p) (h2 : (2 : ZMod p) ≠ 0) : constantCoeff (WFz p a 1) = 1 := by
  have e : constantCoeff (WFz p a 1) = (2 : ZMod p)⁻¹ * (1 + 1) := by
    show constantCoeff (C (2 : ZMod p)⁻¹ * (1 + rhoWF p a)) = _
    rw [map_mul, map_add, map_one, rhoWF_const, constantCoeff_C]
  rw [e, one_add_one_eq_two, inv_mul_cancel₀ h2]
lemma WFg0_const (p : ℕ) [Fact p.Prime] (a : ZMod p) (h2 : (2 : ZMod p) ≠ 0) : constantCoeff (WFg p a 0) = 1 := by
  have e1 : constantCoeff (1 - X : PowerSeries (ZMod p)) = 1 := by
    rw [map_sub, map_one, constantCoeff_X]; exact sub_zero (1 : ZMod p)
  have e : constantCoeff (WFg p a 0) = 2 * 1 * (1 * (1 + 1))⁻¹ := by
    show constantCoeff (C (2 : ZMod p) * rhoWF p a * ((1 - X) * (1 + rhoWF p a))⁻¹) = _
    rw [map_mul, map_mul, constantCoeff_inv, map_mul, e1, map_add, map_one, rhoWF_const,
      constantCoeff_C]
  rw [e, one_mul, mul_one, one_add_one_eq_two, mul_inv_cancel₀ h2]
lemma WFg1_const (p : ℕ) [Fact p.Prime] (a : ZMod p) : constantCoeff (WFg p a 1) = 1 + 1 := by
  show constantCoeff ((1 + rhoWF p a) * (rhoWF p a)⁻¹) = _
  rw [map_mul, constantCoeff_inv, map_add, map_one, rhoWF_const, inv_one, mul_one]
lemma WFz0_coeff1 (p : ℕ) [Fact p.Prime] (a : ZMod p) : coeff 1 (WFz p a 0) = (2 : ZMod p)⁻¹ * (0 - a * (2 : ZMod p)⁻¹) := by
  show coeff 1 (C (2 : ZMod p)⁻¹ * (1 - rhoWF p a)) = _
  rw [coeff_C_mul, map_sub, coeff_one, rhoWF_coeff1, if_neg Nat.one_ne_zero]; rfl
lemma WFz1_coeff1 (p : ℕ) [Fact p.Prime] (a : ZMod p) : coeff 1 (WFz p a 1) = (2 : ZMod p)⁻¹ * (0 + a * (2 : ZMod p)⁻¹) := by
  show coeff 1 (C (2 : ZMod p)⁻¹ * (1 + rhoWF p a)) = _
  rw [coeff_C_mul, map_add, coeff_one, rhoWF_coeff1, if_neg Nat.one_ne_zero]

/-- **`thm:WF`** (`t = 0`): both brick walls are `(0,2)`-sequences in base `p ≥ 5`. -/
theorem WF_net (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1) :
    IsSeq0 (zcode p) (WFgen p a) := by
  have h2 := two_ne_zero_zmod p (by omega)
  have h2i : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  have ha0 : a ≠ 0 := by
    rcases ha with rfl | rfl
    · exact f_one_ne
    · exact f_neg_one_ne
  have h01 : constantCoeff (WFz p a 0) ≠ constantCoeff (WFz p a 1) := by
    rw [WFz0_const, WFz1_const p a h2]; exact zero_ne_one
  refine ss_t0 (zcode p) _ _ ?_ ?_ ?_
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd hxy h01
    · exact absurd hxy.symm h01
    · rfl
  · intro c
    fin_cases c
    · show constantCoeff (WFg p a 0) ≠ 0
      rw [WFg0_const p a h2]; exact f_one_ne
    · show constantCoeff (WFg p a 1) ≠ 0
      rw [WFg1_const, one_add_one_eq_two]; exact h2
  · intro c
    fin_cases c
    · show coeff 1 (WFz p a 0) ≠ 0
      rw [WFz0_coeff1, zero_sub]
      exact f_mul_ne h2i (f_neg_ne (f_mul_ne ha0 h2i))
    · show coeff 1 (WFz p a 1) ≠ 0
      rw [WFz1_coeff1, zero_add]
      exact f_mul_ne h2i (f_mul_ne ha0 h2i)

/-! ### The base-2 sequence -/

lemma uB2coeff_zero : uB2coeff 0 = 0 := by decide
lemma uB2coeff_one : uB2coeff 1 = 1 := by decide

/-- **`thm:B2`** (`t = 0`): the base-2 sequence is a `(0,2)`-sequence. -/
theorem B2_net : IsSeq0 (zcode 2) B2gen := by
  have hu0 : constantCoeff uB2 = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, uB2, coeff_mk, uB2coeff_zero]
  have hu1 : coeff 1 uB2 = 1 := by rw [uB2, coeff_mk, uB2coeff_one]
  have h01 : constantCoeff (B2z 0) ≠ constantCoeff (B2z 1) := by
    show constantCoeff uB2 ≠ constantCoeff (1 + uB2)
    rw [map_add, map_one, hu0]; decide
  refine ss_t0 (zcode 2) _ _ ?_ ?_ ?_
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd hxy h01
    · exact absurd hxy.symm h01
    · rfl
  · intro c
    fin_cases c
    · show constantCoeff ((1 + X) * (1 + uB2)) ≠ 0
      rw [map_mul, map_add, map_add, map_one, constantCoeff_X, hu0]; decide
    · show constantCoeff (mk fun n => uB2coeff (n + 1)) ≠ 0
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, uB2coeff_one]; decide
  · intro c
    fin_cases c
    · show coeff 1 uB2 ≠ 0
      rw [hu1]; decide
    · show coeff 1 (1 + uB2) ≠ 0
      rw [map_add, coeff_one, hu1]; decide

end GeoSeq
