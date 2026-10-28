/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S11Res

@[expose] public section

/-!
# GeoSeq stage S11: the local roots of the Faure frame and the change of coordinate `w ↔ t`

At the place `a_c` the frame polynomial is `w = t (t + δ_c)` in the coordinate `t = z - a_c`
(`wD δ = X (X + δ)`). Substituting `w = wD δ` into a series in `w` (`PowerSeries.subst`) expresses it in
the coordinate `t`.

* `tRoot_add_sq`: `T + T² = w`; `tRoot_subst_wD`: `T(t(t + δ)) = δ t` (`δ² = 1`).
* `gamF_subst_wD`: `γ(t (t + δ)) = (t + δ)²` (`γ = z_1² = (z_0 - 1)²`); `gamF_zero`, `gamF_one`
  (`γ_0 = 1`, `γ_1 = 2`); `gamF_odd` (characteristic two: `γ` is even).
* `coeff_subst_mul`: `[t^j] (f(w) · Q) = ∑_{d ≤ j} f_d [t^j] (w^d Q)` (`w = wD δ`).
* `coeff_change`: `[w^j] f = [t^j] f(wD δ) · (2t + δ) (t + δ)^{-j-1}` (the residue is invariant under the
  change of coordinate; proved by the binomial identity `binom(2d, d) = 2 binom(2d-1, d-1)`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

lemma constantCoeff_wD (δ : F) : constantCoeff (wD δ) = 0 := by simp [wD]

lemma hasSubst_wD (δ : F) : HasSubst (wD δ) := HasSubst.of_constantCoeff_zero' (constantCoeff_wD δ)

lemma hasSubst_wLoc : HasSubst (wLoc : PS) :=
  HasSubst.of_constantCoeff_zero' (by simp [wLoc])

lemma constantCoeff_wLoc : constantCoeff (wLoc : PS) = 0 := by simp [wLoc]

lemma constantCoeff_tRoot : constantCoeff (tRoot : PS) = 0 := by
  simp [tRoot]

lemma hasSubst_tRoot : HasSubst (tRoot : PS) := HasSubst.of_constantCoeff_zero' constantCoeff_tRoot

lemma coeff_one_tRoot : coeff 1 (tRoot : PS) = 1 := by
  rw [tRoot, coeff_one_substInvOfIsUnit]
  have h : coeff 1 (wLoc : PS) = 1 := by simp [wLoc, coeff_X_pow]
  have : (isUnit_coeff_one_wLoc (F := F)).unit = 1 := Units.ext h
  rw [this, inv_one, Units.val_one]

/-- `T + T² = w`. -/
lemma tRoot_add_sq : (tRoot : PS) + tRoot ^ 2 = X := by
  have h := subst_substInvOfIsUnit_right (wLoc : PS) constantCoeff_wLoc isUnit_coeff_one_wLoc
  rw [← tRoot, wLoc, subst_add hasSubst_tRoot, subst_pow hasSubst_tRoot,
    subst_X hasSubst_tRoot] at h
  exact h

/-- `T(t + t²) = t`. -/
lemma tRoot_subst_wLoc : (tRoot : PS).subst (wLoc : PS) = X :=
  subst_substInvOfIsUnit_left (wLoc : PS) constantCoeff_wLoc isUnit_coeff_one_wLoc

lemma hasSubst_CX (δ : F) : HasSubst (C δ * X : PS) :=
  HasSubst.of_constantCoeff_zero' (by simp)

lemma subst_CX_X (δ : F) : (X : PS).subst (C δ * X : PS) = C δ * X := subst_X (hasSubst_CX δ)

/-- `wLoc(δ t) = t (t + δ)` for `δ² = 1`. -/
lemma wLoc_subst_CX (δ : F) (hδ : δ * δ = 1) : (wLoc : PS).subst (C δ * X : PS) = wD δ := by
  rw [wLoc, subst_add (hasSubst_CX δ), subst_pow (hasSubst_CX δ), subst_X (hasSubst_CX δ), wD]
  have : (C δ * C δ : PS) = 1 := by rw [← map_mul, hδ, map_one]
  linear_combination (X * X : PS) * this

/-- `T(t (t + δ)) = δ t` for `δ² = 1`. -/
lemma tRoot_subst_wD (δ : F) (hδ : δ * δ = 1) : (tRoot : PS).subst (wD δ) = C δ * X := by
  rw [← wLoc_subst_CX δ hδ, ← subst_comp_subst_apply hasSubst_wLoc (hasSubst_CX δ),
    tRoot_subst_wLoc, subst_X (hasSubst_CX δ)]

/-- The substitution `w ↦ wD δ` as a ring homomorphism. -/
lemma subst_wD_one (δ : F) : (1 : PS).subst (wD δ) = 1 := by
  rw [← coe_substAlgHom (hasSubst_wD δ), map_one]

lemma subst_wD_C (δ a : F) : (C a : PS).subst (wD δ) = C a := by
  rw [subst_C]; rfl

/-- `γ(t (t + δ)) = (t + δ)²` for `δ² = 1`. -/
lemma gamF_subst_wD (δ : F) (hδ : δ * δ = 1) : (gamF : PS).subst (wD δ) = (X + C δ) ^ 2 := by
  rw [gamF, subst_pow (hasSubst_wD δ), subst_add (hasSubst_wD δ), subst_wD_one, tRoot_subst_wD δ hδ]
  have : (C δ * C δ : PS) = 1 := by rw [← map_mul, hδ, map_one]
  linear_combination (X * X - 1 : PS) * this

lemma gamF_zero : coeff 0 (gamF : PS) = 1 := by
  rw [gamF, coeff_zero_eq_constantCoeff_apply, map_pow, map_add, map_one, constantCoeff_tRoot,
    add_zero, one_pow]

lemma gamF_one : coeff 1 (gamF : PS) = 2 := by
  rw [gamF, show (1 + tRoot : PS) ^ 2 = 1 + 2 * tRoot + tRoot * tRoot by ring, map_add, map_add,
    coeff_one, (map_ofNat C 2).symm, coeff_C_mul, coeff_one_tRoot, coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.Nat.antidiagonal_zero]
  simp [constantCoeff_tRoot]

/-- In characteristic two `γ = 1 + T²` has only even coefficients. -/
lemma gamF_odd (h2 : (2 : F) = 0) (n : ℕ) (hn : n % 2 = 1) : coeff n (gamF : PS) = 0 := by
  have h2' : (2 : PS) = 0 := by rw [(map_ofNat C 2).symm, h2, map_zero]
  rw [gamF, show (1 + tRoot : PS) ^ 2 = 1 + 2 * tRoot + tRoot * tRoot by ring, h2', zero_mul,
    add_zero, map_add, coeff_one, ite_eq_right (by omega), zero_add, coeff_mul]
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p hp _ h => ?_)
    (fun p hp => ?_) (fun p _ => by simp)
  · show coeff p.1 tRoot * coeff p.2 tRoot + coeff p.2 tRoot * coeff p.1 tRoot = 0
    rw [mul_comm (coeff p.2 _), ← two_mul, h2, zero_mul]
  · have h1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have : p.1 = p.2 := by
      have := congrArg Prod.fst h; simpa using this.symm
    omega
  · have h1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only [Prod.fst_swap, Prod.snd_swap]; omega)


/-- `(t + δ)^e (t + δ)^{-E} = (t + δ)^{-(E - e)}` for `e ≤ E`, `δ ≠ 0`. -/
lemma pow_mul_inv_pow (δ : F) (hδ : δ ≠ 0) (e E : ℕ) (h : e ≤ E) :
    (X + C δ : PS) ^ e * ((X + C δ) ^ E)⁻¹ = ((X + C δ) ^ (E - e))⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (constantCoeff_X_add_C_pow_ne δ hδ _), mul_assoc,
    mul_comm _ ((X + C δ : PS) ^ (E - e)), ← mul_assoc, ← pow_add, show e + (E - e) = E by omega]
  exact PowerSeries.mul_inv_cancel _ (constantCoeff_X_add_C_pow_ne δ hδ _)

/-- **Coefficients of a substituted series**: `[t^j] (f(w) · Q) = ∑_{d ≤ j} f_d [t^j] (w^d Q)`
for `w(0) = 0`. -/
lemma coeff_subst_mul (w : PS) (hw : constantCoeff w = 0) (f Q : PS) (j : ℕ) :
    coeff j (f.subst w * Q) = ∑ d ∈ range (j + 1), coeff d f * coeff j (w ^ d * Q) := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw
  set f' : PS := (trunc (j + 1) f : PS)
  obtain ⟨h, hh⟩ : X ^ (j + 1) ∣ f - f' := by
    refine X_pow_dvd_iff.2 fun m hm => ?_
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, ite_eq_left hm, sub_self]
  have hf : f = f' + X ^ (j + 1) * h := by rw [← hh]; ring
  obtain ⟨w1, hw1⟩ := X_dvd_iff.2 hw
  have hsub : f.subst w = f'.subst w + X ^ (j + 1) * (w1 ^ (j + 1) * h.subst w) := by
    conv_lhs => rw [hf]
    rw [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, hw1]
    ring
  rw [hsub, add_mul, map_add, mul_assoc, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]
  rw [subst_coe hs, Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt f j), Finset.sum_mul,
    map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [coeff_trunc, ite_eq_left (by simpa using hd), smul_mul_assoc, map_smul, smul_eq_mul]

lemma choose_two_mul (k : ℕ) : (2 * (k + 1)).choose (k + 1) = 2 * (2 * k + 1).choose k := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ,
    show (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k by
      rw [Nat.choose_symm_of_eq_add]; ring]
  ring

/-- `[t^e] (2t + δ) (t + δ)^{-(e+1)} = 0` for `e ≥ 1`, `δ² = 1`. -/
lemma coeff_change_kernel (δ : F) (hδ : δ * δ = 1) (e : ℕ) (he : 1 ≤ e) :
    coeff e ((C 2 * X + C δ : PS) * ((X + C δ) ^ (e + 1))⁻¹) = 0 := by
  have hδ0 : δ ≠ 0 := fun h => by simp [h] at hδ
  have hsplit : (C 2 * X + C δ : PS) * ((X + C δ) ^ (e + 1))⁻¹ =
      C 2 * ((X + C δ) ^ e)⁻¹ - C δ * ((X + C δ) ^ (e + 1))⁻¹ := by
    have h1 : (X + C δ : PS) ^ 1 * ((X + C δ) ^ (e + 1))⁻¹ = ((X + C δ) ^ e)⁻¹ := by
      rw [pow_mul_inv_pow δ hδ0 1 (e + 1) (by omega), Nat.add_sub_cancel]
    rw [pow_one] at h1
    rw [← h1, show (C 2 : PS) = 2 from map_ofNat C 2]; ring
  rw [hsplit, map_sub, coeff_C_mul, coeff_C_mul, coeff_inv_pow δ hδ e e he,
    coeff_inv_pow δ hδ (e + 1) e (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hc : ((k + 1 + (k + 1)).choose (k + 1) : F) = 2 * ((k + (k + 1)).choose k : F) := by
    rw [show k + 1 + (k + 1) = 2 * (k + 1) by ring, choose_two_mul,
      show k + (k + 1) = 2 * k + 1 by ring]
    push_cast; ring
  rw [hc]
  have hp : ∀ n : ℕ, δ ^ n * (-δ) ^ n = (-1) ^ n := fun n => by
    rw [← mul_pow, show δ * -δ = -1 by linear_combination -hδ]
  have : (δ * (δ ^ (k + 1 + 1) * (-δ) ^ (k + 1))) = (-1) ^ (k + 1) := by
    rw [pow_succ, show δ * (δ ^ (k + 1) * δ * (-δ) ^ (k + 1)) =
      (δ * δ) * (δ ^ (k + 1) * (-δ) ^ (k + 1)) by ring, hδ, one_mul, hp]
  linear_combination (2 * ((k + (k + 1)).choose k : F)) * hp (k + 1) -
    (2 * ((k + (k + 1)).choose k : F)) * this

/-- **Change of coordinate** `w ↔ t` (the residue is invariant): `[w^j] f = [t^j] f(t(t + δ)) ·
(2t + δ) (t + δ)^{-(j+1)}`, `δ² = 1`. Here `(2t + δ) dt = dw` and `w^{-j-1} = t^{-j-1} (t + δ)^{-j-1}`. -/
lemma coeff_change (δ : F) (hδ : δ * δ = 1) (f : PS) (j : ℕ) :
    coeff j f = coeff j (f.subst (wD δ) * ((C 2 * X + C δ) * ((X + C δ) ^ (j + 1))⁻¹)) := by
  have hδ0 : δ ≠ 0 := fun h => by simp [h] at hδ
  rw [coeff_subst_mul (wD δ) (constantCoeff_wD δ), Finset.sum_eq_single j]
  · rw [wD, mul_pow, mul_assoc, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
      mul_left_comm, pow_mul_inv_pow δ hδ0 j (j + 1) (by omega), Nat.add_sub_cancel_left, pow_one]
    have : coeff 0 ((C 2 * X + C δ : PS) * (X + C δ)⁻¹) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv]
      simp [hδ0]
    rw [this, mul_one]
  · intro d hd hdj
    have hdj' : d < j := by simp at hd; omega
    rw [wD, mul_pow, mul_assoc, coeff_X_pow_mul', ite_eq_left (by omega), mul_left_comm,
      pow_mul_inv_pow δ hδ0 d (j + 1) (by omega), show j + 1 - d = (j - d) + 1 by omega,
      coeff_change_kernel δ hδ (j - d) (by omega), mul_zero]
  · intro h; simp at h

/-- **The curvature identity**: `[t^K] P (t + δ)^{-K} = ∑_{n ≤ K} γ_n [t^{K-n}] P (t + δ)^{-(K-n+2)}`
(`δ² = 1`): the polar part of `w^{-K} dz/(z - a_{1-c})` at `a_c` in the e-basis, from
`(t + δ)² = γ(t(t + δ))`. -/
lemma gam_expand (δ : F) (hδ : δ * δ = 1) (P : PS) (K : ℕ) :
    coeff K (P * ((X + C δ) ^ K)⁻¹) =
      ∑ n ∈ range (K + 1), coeff n gamF * coeff (K - n) (P * ((X + C δ) ^ (K - n + 2))⁻¹) := by
  have hδ0 : δ ≠ 0 := fun h => by simp [h] at hδ
  have hL : P * ((X + C δ) ^ K)⁻¹ = (gamF : PS).subst (wD δ) * (P * ((X + C δ) ^ (K + 2))⁻¹) := by
    rw [gamF_subst_wD δ hδ, mul_left_comm, pow_mul_inv_pow δ hδ0 2 (K + 2) (by omega),
      Nat.add_sub_cancel]
  rw [hL, coeff_subst_mul (wD δ) (constantCoeff_wD δ)]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnK : n ≤ K := by simp at hn; omega
  rw [wD, mul_pow, mul_assoc, coeff_X_pow_mul', ite_eq_left hnK, mul_left_comm,
    pow_mul_inv_pow δ hδ0 n (K + 2) (by omega), show K + 2 - n = K - n + 2 by omega]

end GeoSeq
