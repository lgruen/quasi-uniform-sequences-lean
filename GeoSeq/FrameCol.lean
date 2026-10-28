/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Faure2
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S10: one column of the law of a self-similar scramble, any frame (`prop:LI`(c))

Setting: a frame over a field `F` given by a monic `w` of degree `s` and scaled local roots
`zθ c = z_c(θx)` with `w(z_c(θx)) = θx` and distinct places `a_c = z_c(0)`; multipliers `g_c` with
`g_c(0) ≠ 0`; any right inverse `G` of the frame matrix `M = frameM g zθ`. Fix a column `c'`.

* `colH G c'` = `H(Z) = ∑_b G[b][c'] Z^b` (a polynomial over `F[[x]]`): `g_c H(z_c) = δ_{cc'}`
  (`colH_root`), so `H` vanishes at the `s - 1` roots `z_c`, `c ≠ c'`.
* `colP c'` = `P(Z) = ∏_{c ≠ c'} (Z - z_c)`; **`colH_eq`**: `H = λ P` with `λ g_{c'} P(z_{c'}) = 1`.
* `frame_factor`: `w(Z) - θx = ∏_c (Z - z_c)` over `F[[x]]` (monic of degree `s` with `s` distinct roots).
* `law_col`: `D(l)[c][c'] = [x^l] (δ_{cc'} - g_c(0) λ P(a_c)) / (1-x)`; `colP_cross`:
  `(a_c - z_{c'}) P(a_c) = -θx` for `c ≠ c'`; `colP_own`: `P(a_{c'}) = ∏_{c ≠ c'} (z_{c'} - a_c)`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

/-- The column polynomial `H(Z) = ∑_b G[b][c'] Z^b`. -/
noncomputable def colH (G : Matrix (Fin s) (Fin s) PS) (c' : Fin s) : PS[X] :=
  ∑ b : Fin s, Polynomial.monomial (b : ℕ) (G b c')

/-- `P(Z) = ∏_{c ≠ c'} (Z - z_c)`. -/
noncomputable def colP (zθ : Fin s → PS) (c' : Fin s) : PS[X] :=
  ∏ c ∈ univ.erase c', (Polynomial.X - Polynomial.C (zθ c))

lemma colH_eval (G : Matrix (Fin s) (Fin s) PS) (c' : Fin s) (z : PS) :
    (colH G c').eval z = ∑ b : Fin s, G b c' * z ^ (b : ℕ) := by
  simp [colH, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

lemma colH_natDegree (G : Matrix (Fin s) (Fin s) PS) (c' : Fin s) :
    (colH G c').natDegree < s := by
  have hs : 0 < s := Fin.pos c'
  have : (colH G c').natDegree ≤ s - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ =>
      (Polynomial.natDegree_monomial_le _).trans (by have := b.isLt; omega)
  omega

lemma colH_root (g zθ : Fin s → PS) (G : Matrix (Fin s) (Fin s) PS)
    (hMG : frameM g zθ * G = 1) (c c' : Fin s) :
    g c * (colH G c').eval (zθ c) = if c = c' then 1 else 0 := by
  have h := congrFun (congrFun hMG c) c'
  simp only [Matrix.mul_apply, frameM, Matrix.one_apply] at h
  rw [colH_eval, Finset.mul_sum, ← h]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma colP_eval_ne (zθ : Fin s → PS) {c c' : Fin s} (h : c ≠ c') : (colP zθ c').eval (zθ c) = 0 := by
  rw [colP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ c⟩) (by simp)

lemma colP_natDegree (zθ : Fin s → PS) (c' : Fin s) : (colP zθ c').natDegree < s := by
  have hs : 0 < s := Fin.pos c'
  have h1 : (colP zθ c').natDegree ≤ ∑ c ∈ univ.erase c', 1 :=
    (Polynomial.natDegree_prod_le _ _).trans
      (Finset.sum_le_sum fun c _ => Polynomial.natDegree_X_sub_C_le _)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at h1
  omega

lemma constantCoeff_colP_eval (zθ : Fin s → PS) (c' : Fin s) (z : PS) :
    constantCoeff ((colP zθ c').eval z) =
      ∏ c ∈ univ.erase c', (constantCoeff z - constantCoeff (zθ c)) := by
  simp [colP, Polynomial.eval_prod, map_prod]

lemma colP_unit (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) :
    constantCoeff ((colP zθ c').eval (zθ c')) ≠ 0 := by
  rw [constantCoeff_colP_eval]
  refine Finset.prod_ne_zero_iff.2 fun c hc => sub_ne_zero.2 fun h => ?_
  exact (Finset.mem_erase.1 hc).1 (hinj h.symm)

lemma zθ_injective (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) :
    Function.Injective zθ := fun c c'' h => hinj (by simp [ssPlace, h])

/-- **`H = λ P`** with `λ = H(z_{c'}) / P(z_{c'})`. -/
lemma colH_eq (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (G : Matrix (Fin s) (Fin s) PS)
    (hMG : frameM g zθ * G = 1) (c' : Fin s) :
    colH G c' = Polynomial.C ((colH G c').eval (zθ c') * ((colP zθ c').eval (zθ c'))⁻¹) *
      colP zθ c' := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (zθ_injective zθ hinj) (fun c => ?_) ?_
  · rw [Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hc : c = c'
    · subst hc
      rw [mul_assoc, PowerSeries.inv_mul_cancel _ (colP_unit zθ hinj c), mul_one]
    · rw [colP_eval_ne zθ hc, mul_zero]
      have h := colH_root g zθ G hMG c c'
      rw [if_neg hc] at h
      have hg0 : g c ≠ 0 := fun h0 => hg c (by rw [h0, map_zero])
      exact (mul_eq_zero.1 h).resolve_left hg0
  · rw [Fintype.card_fin]
    refine max_lt (colH_natDegree G c') ?_
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (colP_natDegree zθ c')

/-- `λ g_{c'} P(z_{c'}) = 1`. -/
lemma colLam_spec (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (G : Matrix (Fin s) (Fin s) PS)
    (hMG : frameM g zθ * G = 1) (c' : Fin s) :
    (colH G c').eval (zθ c') * ((colP zθ c').eval (zθ c'))⁻¹ * g c' *
      (colP zθ c').eval (zθ c') = 1 := by
  have h := colH_root g zθ G hMG c' c'
  rw [if_pos rfl] at h
  rw [mul_assoc, mul_comm (g c'), ← mul_assoc, mul_assoc _ _ ((colP zθ c').eval (zθ c')),
    PowerSeries.inv_mul_cancel _ (colP_unit zθ hinj c'), mul_one, mul_comm, h]

/-- The one-digit law of column `c'` through `H`: `D(l)[c][c'] = [x^l](δ - g_c(0) H(a_c))/(1-x)`. -/
lemma law_colH (g zθ : Fin s → PS) (G : Matrix (Fin s) (Fin s) PS) (l : ℕ) (c c' : Fin s) :
    lawD g zθ G 0 l c c' =
      coeff l ((PowerSeries.C (if c = c' then (1 : F) else 0) -
        PowerSeries.C (constantCoeff (g c)) *
          (colH G c').eval (PowerSeries.C (constantCoeff (zθ c)))) * PowerSeries.mk 1) := by
  rw [lawD_zero, colH_eval, sub_mul, map_sub, Finset.mul_sum, Finset.sum_mul, map_sum]
  congr 1
  · split_ifs <;> simp [PowerSeries.coeff_mk]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have e : PowerSeries.C (constantCoeff (g c)) * (G b c' * PowerSeries.C (constantCoeff (zθ c)) ^
        (b : ℕ)) * PowerSeries.mk 1 =
        PowerSeries.C (constantCoeff (g c) * constantCoeff (zθ c) ^ (b : ℕ)) *
          (G b c' * PowerSeries.mk 1) := by rw [map_mul, map_pow]; ring
    rw [e, PowerSeries.coeff_C_mul, frameM, map_mul, map_pow]

end GeoSeq
