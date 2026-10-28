/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.FrameLI
public import GeoSeq.Rational

@[expose] public section

/-!
# GeoSeq stage S10: `prop:N2` (no periodic law)

The carry responses are taken semantically (`IsCarryEntry`, every level `K ≥ l`), and the law series is
their generating function `∑_l D(l) x^l` (rational iff the series of law coefficients is rational,
`isRat_partial`; eventually periodic ⟹ rational, `evPeriodic_isRat`).

* **`N2a`** (`prop:N2`(a), self-similar part): Faure frame (`s = 2`, places `0, 1`), any finite field,
  any multipliers: the own responses of coordinate `1` and the cross responses `0 ← 1` are not both
  rational, and not both eventually periodic (`N2a_periodic`).
* **`N2b`** (`prop:N2`(b)): any frame with `s ≥ 3` (any monic `w` of degree `s` with the local roots),
  two cross responses `c₁ ← c'`, `c₂ ← c'` of one column are not both rational (`N2b_periodic`).
* The clause of (a) for every scramble with a level-invariant law (`q` odd or `q = 2`) rests on
  `prop:LIconv`, which is not formalized (gap, see the research notes).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

lemma isRat_of_coeff_eq {f g : PS} (h : ∀ n, 1 ≤ n → coeff n f = coeff n g) (hf : IsRatPS f) :
    IsRatPS g := by
  have e : g = f + PowerSeries.C (constantCoeff g - constantCoeff f) := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [map_add, PowerSeries.coeff_C, if_neg (by omega), add_zero, h n hn]
  rw [e]; exact hf.add (isRat_C _)

/-- Carry responses given at every level agree with the law. -/
lemma resp_eq_law [Fintype F] [DecidableEq F] {s : ℕ} (g zθ : Fin s → PS) (w : F[X])
    (hw : w.natDegree ≤ s) (θ : F) (hθ : θ ≠ 0)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (G : Matrix (Fin s) (Fin s) PS) (hMG : frameM g zθ * G = 1) (c c' : Fin s) (x : ℕ → F)
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c c' (x l)) (l : ℕ) (hl : 1 ≤ l) :
    x l = lawD g zθ G 0 l c c' :=
  carryEntry_unique _ _ _ _ _ _ (hx l l hl le_rfl)
    (law g zθ w hw θ θ⁻¹ (mul_inv_cancel₀ hθ) hroot G hMG l 0 l hl le_rfl c c')

/-- **`prop:N2`(b)**: for a self-similar scramble of any frame with `s ≥ 3`, two cross responses
`c₁ ← c'` and `c₂ ← c'` of the same column (`c₁ ≠ c₂`, both `≠ c'`) do not both have rational generating
functions `∑_l D(l)[c_i][c'] x^l`. -/
theorem N2b [Fintype F] [DecidableEq F] {s : ℕ} (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s)
    (θ : F) (hθ : θ ≠ 0) (g zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (c₁ c₂ c' : Fin s) (h12 : c₁ ≠ c₂) (h1 : c₁ ≠ c') (h2 : c₂ ≠ c') (x₁ x₂ : ℕ → F)
    (hx₁ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₁ c' (x₁ l))
    (hx₂ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₂ c' (x₂ l)) :
    ¬ (IsRatPS (PowerSeries.mk x₁) ∧ IsRatPS (PowerSeries.mk x₂)) := by
  rintro ⟨hr1, hr2⟩
  obtain ⟨G, hMG, -⟩ := frame_inv g zθ hinj hg
  set lam := (colH G c').eval (zθ c') * ((colP zθ c').eval (zθ c'))⁻¹ with hlam
  have hH := colH_eq g zθ hinj hg G hMG c'
  rw [← hlam] at hH
  have hlam0 : lam ≠ 0 := by
    intro h0
    have := colLam_spec g zθ hinj hg G hMG c'
    rw [← hlam, h0] at this
    simp at this
  -- the series `T_c = g_c(0) λ θ x / (a_c - z_{c'})` with partial sums `D(l)[c][c']`
  have key : ∀ c, c ≠ c' → ∀ x : ℕ → F,
      (∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c c' (x l)) →
      IsRatPS (PowerSeries.mk x) →
      IsRatPS (C (constantCoeff (g c)) * lam * C θ * X * (C (ssPlace zθ c) - zθ c')⁻¹) := by
    intro c hc x hx hr
    have hu : constantCoeff (C (ssPlace zθ c) - zθ c') ≠ 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C]
      exact sub_ne_zero.2 fun h => hc (hinj (by simpa [ssPlace] using h))
    have hP : (colP zθ c').eval (C (ssPlace zθ c)) =
        (C (ssPlace zθ c) - zθ c')⁻¹ * (-(C θ * X)) := by
      rw [← colP_cross w hw hdeg θ zθ hroot hinj c c', ← mul_assoc,
        PowerSeries.inv_mul_cancel _ hu, one_mul]
    rw [← isRat_partial]
    refine isRat_of_coeff_eq (fun n hn => ?_) hr
    rw [PowerSeries.coeff_mk, resp_eq_law g zθ w hdeg.le θ hθ hroot G hMG c c' x hx n hn, law_colH,
      if_neg hc, map_zero, hH, Polynomial.eval_mul, Polynomial.eval_C, cc_eq_place zθ c, hP]
    congr 1; ring
  have hT1 := key c₁ h1 x₁ hx₁ hr1
  have hT2 := key c₂ h2 x₂ hx₂ hr2
  set u1 := (C (ssPlace zθ c₁) - zθ c') with hu1
  set u2 := (C (ssPlace zθ c₂) - zθ c') with hu2
  have hu1' : constantCoeff u1 ≠ 0 := by
    rw [hu1, map_sub, PowerSeries.constantCoeff_C]
    exact sub_ne_zero.2 fun h => h1 (hinj (by simpa [ssPlace] using h))
  have hu2' : constantCoeff u2 ≠ 0 := by
    rw [hu2, map_sub, PowerSeries.constantCoeff_C]
    exact sub_ne_zero.2 fun h => h2 (hinj (by simpa [ssPlace] using h))
  set T1 := C (constantCoeff (g c₁)) * lam * C θ * X * u1⁻¹
  set T2 := C (constantCoeff (g c₂)) * lam * C θ * X * u2⁻¹
  set k1 := C (constantCoeff (g c₁))
  set k2 := C (constantCoeff (g c₂))
  have e1 : T1 * u1 = k1 * lam * C θ * X := by
    simp only [T1]; rw [mul_assoc _ u1⁻¹, PowerSeries.inv_mul_cancel _ hu1', mul_one]
  have e2 : T2 * u2 = k2 * lam * C θ * X := by
    simp only [T2]; rw [mul_assoc _ u2⁻¹, PowerSeries.inv_mul_cancel _ hu2', mul_one]
  have hk1 : k1 ≠ 0 := fun h => hg c₁ (by simpa [k1] using congrArg constantCoeff h)
  have hk2 : k2 ≠ 0 := fun h => hg c₂ (by simpa [k2] using congrArg constantCoeff h)
  have hX0 : (X : PS) ≠ 0 := PowerSeries.X_ne_zero
  have hCθ : C θ ≠ (0 : PS) := fun h => hθ (by simpa using congrArg constantCoeff h)
  have hT1ne : T1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hk1 hlam0) hCθ) hX0 e1.symm
  -- `z_{c'} (k1 T2 - k2 T1) = k1 T2 a_{c₂} - k2 T1 a_{c₁}`
  set D := k1 * T2 - k2 * T1
  have hz : D * zθ c' = k1 * T2 * C (ssPlace zθ c₂) - k2 * T1 * C (ssPlace zθ c₁) := by
    have : k2 * (T1 * u1) = k1 * (T2 * u2) := by rw [e1, e2]; ring
    simp only [D]; rw [hu1, hu2] at this; linear_combination this
  have hD : D ≠ 0 := by
    intro h0
    have h' : k1 * T2 = k2 * T1 := sub_eq_zero.1 h0
    have : k2 * (T1 * u1) = k1 * (T2 * u2) := by rw [e1, e2]; ring
    rw [show k1 * (T2 * u2) = (k1 * T2) * u2 by ring, h', hu1, hu2] at this
    have h3 : k2 * T1 * C (ssPlace zθ c₁ - ssPlace zθ c₂) = 0 := by
      rw [map_sub]; linear_combination this
    have hc12 : C (ssPlace zθ c₁ - ssPlace zθ c₂) ≠ (0 : PS) := by
      intro h; have := congrArg constantCoeff h
      simp only [PowerSeries.constantCoeff_C, map_zero] at this
      exact h12 (hinj (sub_eq_zero.1 this))
    exact mul_ne_zero (mul_ne_zero hk2 hT1ne) hc12 h3
  have hrat : IsRatPS (zθ c') :=
    IsRatPS.of_mul_left (((isRat_C _).mul hT2).mul (isRat_C _) |>.sub
      (((isRat_C _).mul hT1).mul (isRat_C _)))
      (((isRat_C _).mul hT2).sub ((isRat_C _).mul hT1)) hD hz
  have hs3 : 2 ≤ w.natDegree := by
    rw [hdeg]
    have : ({c₁, c₂, c'} : Finset (Fin s)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h1]), Finset.card_pair h2]
    have := Finset.card_le_univ ({c₁, c₂, c'} : Finset (Fin s))
    simp only [Fintype.card_fin] at this
    omega
  exact no_rat_root w hw hs3 θ hθ (zθ c') (hroot c') hrat

/-- `prop:N2`(b), periodic form: the two cross-response sequences are not both eventually periodic. -/
theorem N2b_periodic [Fintype F] [DecidableEq F] {s : ℕ} (w : F[X]) (hw : w.Monic)
    (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0) (g zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (c₁ c₂ c' : Fin s) (h12 : c₁ ≠ c₂) (h1 : c₁ ≠ c') (h2 : c₂ ≠ c') (x₁ x₂ : ℕ → F)
    (hx₁ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₁ c' (x₁ l))
    (hx₂ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₂ c' (x₂ l)) :
    ¬ (EvPeriodic x₁ ∧ EvPeriodic x₂) := fun ⟨p1, p2⟩ =>
  N2b w hw hdeg θ hθ g zθ hroot hinj hg c₁ c₂ c' h12 h1 h2 x₁ x₂ hx₁ hx₂
    ⟨evPeriodic_isRat _ p1, evPeriodic_isRat _ p2⟩

/-- **`prop:N2`(a)** (self-similar part): for a self-similar scramble of the Faure frame (`s = 2`, places
`0, 1`, scaled roots `z_0 + z_1 = 1`, `z_0 z_1 = -θx`, `θ ≠ 0`) over any finite field, the generating
functions of the own responses `D(l)[1][1]` and of the cross responses `D(l)[0][1]` are not both rational. -/
theorem N2a [Fintype F] [DecidableEq F] (θ : F) (hθ : θ ≠ 0) (z0 z1 g0 g1 : PS)
    (hz0 : constantCoeff z0 = 0) (hsum : z0 + z1 = 1) (hprod : z0 * z1 = -(C θ * X))
    (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0) (o x : ℕ → F)
    (ho : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 1 1 (o l))
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 0 1 (x l)) :
    ¬ (IsRatPS (PowerSeries.mk o) ∧ IsRatPS (PowerSeries.mk x)) := by
  rintro ⟨hro, hrx⟩
  have hz1 : constantCoeff z1 = 1 := by
    have := congrArg constantCoeff hsum; rw [map_add, hz0, zero_add, map_one] at this; exact this
  have hρ : constantCoeff (z1 - z0) = 1 := by rw [map_sub, hz1, hz0, sub_zero]
  set k0 := ((z1 - z0) * g0)⁻¹
  set k1 := ((z1 - z0) * g1)⁻¹
  have hk0 : k0 * ((z1 - z0) * g0) = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [map_mul, hρ, one_mul]; exact hg0)
  have hk1 : k1 * ((z1 - z0) * g1) = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [map_mul, hρ, one_mul]; exact hg1)
  have hMG := faure_inv z0 z1 g0 g1 k0 k1 hk0 hk1
  set w : F[X] := Polynomial.X ^ 2 - Polynomial.X
  have hwdeg : w.natDegree = 2 := by
    simp only [w]; rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]; simp
  have hwm : w.Monic := by
    simp only [w]; exact Polynomial.monic_X_pow_sub (by simp)
  have hroot : ∀ c, Polynomial.aeval ((![z0, z1] : Fin 2 → PS) c) w = C θ * X := by
    intro c
    have h1 : z1 = 1 - z0 := by rw [← hsum]; ring
    fin_cases c
    · simp only [w, map_sub, map_pow, Polynomial.aeval_X, Fin.zero_eta, Matrix.cons_val_zero]
      linear_combination (-1 : PS) * hprod + z0 * hsum
    · simp only [w, map_sub, map_pow, Polynomial.aeval_X, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linear_combination (-1 : PS) * hprod + z1 * hsum
  have hG := gform z0 z1 g0 g1 k0 k1 hz0 hsum
  -- the two series
  have hA : IsRatPS (1 - C (constantCoeff g1) * z1 * k1) := by
    rw [← isRat_partial]
    refine isRat_of_coeff_eq (fun n hn => ?_) hro
    rw [PowerSeries.coeff_mk, resp_eq_law _ _ w hwdeg.le θ hθ hroot _ hMG 1 1 o ho n hn]
    exact (hG n).2.2.2
  have hB : IsRatPS (C (constantCoeff g0) * z0 * k1) := by
    rw [← isRat_partial]
    refine isRat_of_coeff_eq (fun n hn => ?_) hrx
    rw [PowerSeries.coeff_mk, resp_eq_law _ _ w hwdeg.le θ hθ hroot _ hMG 0 1 x hx n hn]
    exact (hG n).2.1
  have h1r : IsRatPS (1 : PS) := by simpa using isRat_C (1 : F)
  have hz1k : IsRatPS (z1 * k1) := by
    have : z1 * k1 = C (constantCoeff g1)⁻¹ * (1 - (1 - C (constantCoeff g1) * z1 * k1)) := by
      rw [sub_sub_cancel, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hg1, map_one, one_mul]
    rw [this]; exact (isRat_C _).mul (h1r.sub hA)
  have hz0k : IsRatPS (z0 * k1) := by
    have : z0 * k1 = C (constantCoeff g0)⁻¹ * (C (constantCoeff g0) * z0 * k1) := by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hg0, map_one, one_mul]
    rw [this]; exact (isRat_C _).mul hB
  have hk1r : IsRatPS k1 := by
    have : k1 = z0 * k1 + z1 * k1 := by rw [← add_mul, hsum, one_mul]
    rw [this]; exact hz0k.add hz1k
  have hk1ne : k1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hk1; exact zero_ne_one hk1
  have hz1r : IsRatPS z1 := IsRatPS.of_mul_left hz1k hk1r hk1ne (mul_comm _ _)
  exact no_rat_root w hwm (by rw [hwdeg]) θ hθ z1 (hroot 1) hz1r

/-- `prop:N2`(a), periodic form: the two response sequences are not both eventually periodic. -/
theorem N2a_periodic [Fintype F] [DecidableEq F] (θ : F) (hθ : θ ≠ 0) (z0 z1 g0 g1 : PS)
    (hz0 : constantCoeff z0 = 0) (hsum : z0 + z1 = 1) (hprod : z0 * z1 = -(C θ * X))
    (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0) (o x : ℕ → F)
    (ho : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 1 1 (o l))
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 0 1 (x l)) :
    ¬ (EvPeriodic o ∧ EvPeriodic x) := fun ⟨p1, p2⟩ =>
  N2a θ hθ z0 z1 g0 g1 hz0 hsum hprod hg0 hg1 o x ho hx
    ⟨evPeriodic_isRat _ p1, evPeriodic_isRat _ p2⟩

end GeoSeq
