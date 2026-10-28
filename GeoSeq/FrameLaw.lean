/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.FrameCol

@[expose] public section

/-!
# GeoSeq stage S10: `prop:LI`(c) for every frame, the free series, `prop:depthdir`

* `frame_factor`: `w(Z) - θx = ∏_c (Z - z_c(θx))` over `F[[x]]`; `frame_factor_F`: `w = ∏_c (Z - a_c)`.
* `colP_cross` (`c ≠ c'`): `(a_c - z_{c'}) P(a_c) = -θx`; `colP_own`: `P(a_{c'}) = ∏_{c≠c'} (z_{c'} - a_c)`.
* **`LI_c`** (`prop:LI`(c), any `s ≥ 1`, normalisation `ϖ = dz`): with the free series `ψ = freeSer g zθ c'`,
  `O_{c'} = 1 - ŵ_{c'}(z_{c'}) ψ` and `x X_{c←c'} = -κ_{c←c'} x χ_{cc'}(z_{c'}) ψ`, as identities of the
  one-digit law `D(l) = [x^l]𝒟/(1-x)`.
* `freeSer_const` (`ψ(0) = 1`), `freeSer_free` (every unit series with constant term `1` and every
  `g_{c'}(0)` occur), `freeSer_row` (row `n` of `C_{c'}` depends only on `ψ` up to `x^n`).
* **`depthdir`** (`prop:depthdir`): changing the free series of column `c'` at depth `l` (and not below)
  moves the column `(O^{(l)}, (X^{(l+1)}_{c←c'})_{c≠c'})` by `-Δψ_l · (1, (κ_{c←c'})_c)`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

lemma algebraMap_PS : (algebraMap F PS) = PowerSeries.C := by
  refine RingHom.ext fun r => ?_
  rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

lemma aeval_eq_eval_map (w : F[X]) (z : PS) :
    Polynomial.aeval z w = (w.map PowerSeries.C).eval z := by
  rw [Polynomial.aeval_def, Polynomial.eval_map, algebraMap_PS]

lemma constantCoeff_eval_map (w : F[X]) (z : PS) :
    constantCoeff ((w.map PowerSeries.C).eval z) = w.eval (constantCoeff z) := by
  rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  have : (constantCoeff : PS →+* F).comp PowerSeries.C = RingHom.id F := by
    refine RingHom.ext fun r => ?_; simp
  rw [this]; rfl

lemma eval_place (w : F[X]) (θ : F) (z : PS) (hz : Polynomial.aeval z w = PowerSeries.C θ * X) :
    w.eval (constantCoeff z) = 0 := by
  rw [← constantCoeff_eval_map, ← aeval_eq_eval_map, hz]; simp

/-- **`w(Z) - θx = ∏_c (Z - z_c(θx))`** over `F[[x]]`. -/
lemma frame_factor (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hs : 1 ≤ s) :
    w.map PowerSeries.C - Polynomial.C (PowerSeries.C θ * X) =
      ∏ c, (Polynomial.X - Polynomial.C (zθ c)) := by
  set Pz : PS[X] := ∏ c, (Polynomial.X - Polynomial.C (zθ c)) with hPz
  have hmon : Pz.Monic := Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _
  have hdegP : Pz.natDegree = s := by
    rw [hPz, Polynomial.natDegree_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _]
    simp
  refine sub_eq_zero.1 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
    (zθ_injective zθ hinj) (fun c => ?_) ?_)
  · rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_C, ← aeval_eq_eval_map, hroot c,
      hPz, Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ c) (by simp)]
    ring
  · rw [Fintype.card_fin]
    have : (w.map PowerSeries.C - Polynomial.C (PowerSeries.C θ * X) - Pz).natDegree ≤ s - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C,
        if_neg (by omega)]
      rcases Nat.lt_or_ge s N with h | h
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
      · have hN' : N = s := by omega
        subst hN'
        have h1 : w.coeff w.natDegree = 1 := hw
        have h2 : Pz.coeff Pz.natDegree = 1 := hmon
        rw [hdeg] at h1; rw [hdegP] at h2
        rw [h1, h2]; simp
    omega

/-- `w = ∏_c (Z - a_c)` over `F`. -/
lemma frame_factor_F (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hs : 1 ≤ s) :
    w = ∏ c, (Polynomial.X - Polynomial.C (ssPlace zθ c)) := by
  have h := congrArg (Polynomial.map (constantCoeff : PS →+* F))
    (frame_factor w hw hdeg θ zθ hroot hinj hs)
  rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_C, Polynomial.map_prod] at h
  have hc : (constantCoeff : PS →+* F).comp PowerSeries.C = RingHom.id F := by
    refine RingHom.ext fun r => ?_; simp
  rw [hc, Polynomial.map_id] at h
  simpa [ssPlace] using h

/-- `(a_c - z_{c'}) P(a_c) = -θx` for `c ≠ c'`. -/
lemma colP_cross (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (c c' : Fin s) :
    (PowerSeries.C (ssPlace zθ c) - zθ c') * (colP zθ c').eval (PowerSeries.C (ssPlace zθ c)) =
      -(PowerSeries.C θ * X) := by
  have hs : 1 ≤ s := Fin.pos c'
  have h := congrArg (Polynomial.eval (PowerSeries.C (ssPlace zθ c)))
    (frame_factor w hw hdeg θ zθ hroot hinj hs)
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ c')] at h
  have hp : w.eval (ssPlace zθ c) = 0 := eval_place w θ (zθ c) (hroot c)
  rw [Polynomial.eval_sub, Polynomial.eval_map, Polynomial.eval_C, Polynomial.eval₂_at_apply,
    hp, map_zero, zero_sub, Polynomial.eval_mul] at h
  rw [h, colP, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `P(a_{c'}) = ∏_{c ≠ c'} (z_{c'} - a_c)` (the own kernel `ŵ_{c'}(z_{c'})` times `w'(a_{c'})`). -/
lemma colP_own (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0)
    (zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) :
    (colP zθ c').eval (PowerSeries.C (ssPlace zθ c')) =
      ∏ c ∈ univ.erase c', (zθ c' - PowerSeries.C (ssPlace zθ c)) := by
  have hs : 1 ≤ s := Fin.pos c'
  have h1 := colP_cross w hw hdeg θ zθ hroot hinj c' c'
  have h2 : (zθ c' - PowerSeries.C (ssPlace zθ c')) *
      ∏ c ∈ univ.erase c', (zθ c' - PowerSeries.C (ssPlace zθ c)) = PowerSeries.C θ * X := by
    have h := hroot c'
    rw [aeval_eq_eval_map, frame_factor_F w hw hdeg θ zθ hroot hinj hs, Polynomial.map_prod,
      Polynomial.eval_prod] at h
    rw [← h, ← Finset.mul_prod_erase univ _ (Finset.mem_univ c')]
    simp
  have hne : zθ c' - PowerSeries.C (ssPlace zθ c') ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    have := congrArg (PowerSeries.coeff 1) h2
    simp at this
    exact hθ this.symm
  refine mul_left_cancel₀ hne ?_
  rw [h2]
  have : (zθ c' - PowerSeries.C (ssPlace zθ c')) =
      -(PowerSeries.C (ssPlace zθ c') - zθ c') := by ring
  rw [this, neg_mul, h1, neg_neg]

end GeoSeq
