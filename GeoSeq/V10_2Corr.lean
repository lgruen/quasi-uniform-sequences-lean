/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_2Form
public import GeoSeq.V10_1Joint

@[expose] public section

/-!
# GeoSeq stage V10-2 (part 4): `lem:corrS` and `prop:joint` for `def:selfsim` as written

V9-7 / V10-1 proved `lem:corrS` and `prop:joint` for self-similar scrambles in residue form with RATIONAL local
multipliers (`ssResGen a θ N U`, `φ_c = N_c/U_c`). A self-similar scramble (`def:selfsim`) has power-series local
multipliers `φ = locMul a θ g` (`lem:resform`(b)); its rows `n < K` coincide with those of `ssResGen a θ N 1` for the
truncations `N_c(a_c + t) = φ_c mod t^K` (`ssResGen_truncN`), and the statements at level `K` only read rows `< K`
(`corrRel_congr`) resp. `≤ K` (`carry_congr`). The correction coefficients are explicit:
`v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)` (`corrV`, `corrCoef`, `corrTruncPS_corrCoef`).

* **`selfsim_corrS`** (`lem:corrS`, unconditional, every `K ≥ 1`); `selfsim_corr_of` (any `v`, `χ` with
  `CorrTruncPS`).
* **`selfsim_joint_step`** (`prop:joint`(i)), **`selfsim_joint_ii`** (`prop:joint`(ii)).
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F] {s : ℕ}

local notation "PX" => (PowerSeries.X : PowerSeries F)

lemma taylor_truncN (a : Fin s → F) (φ : Fin s → PowerSeries F) (K : ℕ) (c : Fin s) :
    taylor (a c) (truncN a φ K c) = PowerSeries.trunc K (φ c) := by
  rw [truncN, taylor_apply, comp_assoc]
  simp

lemma eval_truncN (a : Fin s → F) (φ : Fin s → PowerSeries F) (K : ℕ) (hK : 1 ≤ K) (c : Fin s) :
    (truncN a φ K c).eval (a c) = PowerSeries.constantCoeff (φ c) := by
  rw [← taylor_coeff_zero, taylor_truncN, PowerSeries.coeff_trunc,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [show 0 < K by omega]

/-- Below `K`, a series and its truncation have the same products' coefficients. -/
lemma coeff_trunc_mul_low (f A : PowerSeries F) (K n : ℕ) (hn : n < K) :
    PowerSeries.coeff n ((PowerSeries.trunc K f : PowerSeries F) * A) = PowerSeries.coeff n (f * A) := by
  conv_rhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc K f]
  rw [add_mul, map_add, mul_assoc, PowerSeries.coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h => absurd h (by omega)), zero_add]

lemma inv_pow_ps (f : PowerSeries F) (hf : PowerSeries.constantCoeff f ≠ 0) (n : ℕ) :
    (f ^ n)⁻¹ = f⁻¹ ^ n := by
  rw [eq_comm, PowerSeries.eq_inv_iff_mul_eq_one (by rw [map_pow]; exact pow_ne_zero _ hf), ← mul_pow,
    PowerSeries.inv_mul_cancel _ hf, one_pow]

/-- **Rows below `K` of a residue form are those of the truncated rational residue form** `ssResGen a θ N 1`,
`N = truncN a φ K`. -/
theorem ssResGen_truncN (a : Fin s → F) (ha : Function.Injective a) (θ : F) (φ : Fin s → PowerSeries F) (K : ℕ)
    (c : Fin s) (n k : ℕ) (hn : n < K) :
    ssResGen a θ (truncN a φ K) (fun _ => 1) c n k = scrGen a (ssL a θ φ) c n k := by
  rw [scrGen_eq_frDigit, ssL_digit, ssResGen, locRes, ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero n)), Nat.add_sub_cancel,
    one_mul, taylor_mul, taylor_truncN]
  simp only [taylor_pow, Polynomial.coe_mul, Polynomial.coe_pow]
  rw [inv_pow_ps _ (by rw [constantCoeff_taylor]; exact wCo_eval_ne a ha c)]
  congr 1
  rw [show ∀ A B T : PowerSeries F, A * B * T = B * (A * T) from fun A B T => by ring,
    coeff_trunc_mul_low _ _ K n hn, show ∀ A B T : PowerSeries F, B * (A * T) = A * (B * T) from fun A B T => by ring]

/-- `CorrRel` at level `K` reads only the rows `< K`. -/
lemma corrRel_congr {q : ℕ} [NeZero q] (D : DigitCode F q) (C₁ C₂ : Gen s F) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (K : ℕ) (hK : 1 ≤ K) (h : ∀ c n k, n < K → C₁ c n k = C₂ c n k) :
    CorrRel D C₁ v χ K ↔ CorrRel D C₂ v χ K := by
  have hd : ∀ x c n, n < K → seqDigit D C₁ x c n = seqDigit D C₂ x c n := fun x c n hn => by
    simp only [seqDigit]; exact Finset.sum_congr rfl fun k _ => by rw [h c n k hn]
  have key : ∀ x c, seqDigit D C₁ x c (K - 1) + ∑ d ∈ Finset.Ico 1 K, χ c d * seqDigit D C₁ x c (K - 1 - d) =
      seqDigit D C₂ x c (K - 1) + ∑ d ∈ Finset.Ico 1 K, χ c d * seqDigit D C₂ x c (K - 1 - d) := fun x c => by
    rw [hd x c (K - 1) (by omega)]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by rw [hd x c (K - 1 - d) (by omega)]
  simp only [CorrRel, key]

/-- The carry entries at level `K` (geometric digit `K + i`) read only the rows `≤ K + i`. -/
lemma carry_congr (C₁ C₂ : Gen s F) (K i l : ℕ) (c c' : Fin s) (d : F)
    (h : ∀ c n k, n ≤ K + i → C₁ c n k = C₂ c n k) :
    IsCarryEntry C₁ K i l c c' d ↔ IsCarryEntry C₂ K i l c c' d := by
  have hv : ∀ (V : Fin (s * K) → F) c₁ n, n ≤ K + i → vecDigit C₁ V c₁ n = vecDigit C₂ V c₁ n :=
    fun V c₁ n hn => by simp only [vecDigit]; exact Finset.sum_congr rfl fun k _ => by rw [h c₁ n k hn]
  constructor
  · rintro ⟨⟨V, hV⟩, h2⟩
    refine ⟨⟨V, fun c₁ n hn => by rw [← hv V c₁ n (by omega)]; exact hV c₁ n hn⟩, fun V' hV' => ?_⟩
    rw [← hv V' c (K + i) le_rfl]
    exact h2 V' fun c₁ n hn => by rw [hv V' c₁ n (by omega)]; exact hV' c₁ n hn
  · rintro ⟨⟨V, hV⟩, h2⟩
    refine ⟨⟨V, fun c₁ n hn => by rw [hv V c₁ n (by omega)]; exact hV c₁ n hn⟩, fun V' hV' => ?_⟩
    rw [hv V' c (K + i) le_rfl]
    exact h2 V' fun c₁ n hn => by rw [← hv V' c₁ n (by omega)]; exact hV' c₁ n hn

/-- **Power-series correction coefficients give the rational ones of the truncation**:
`CorrTruncPS a θ φ v χ K ⇒ CorrTrunc a θ (truncN a φ K) 1 v χ K`. -/
theorem corrTrunc_of_PS (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (K : ℕ) (h : CorrTruncPS a θ φ v χ K) : CorrTrunc a θ (truncN a φ K) (fun _ => 1) v χ K := by
  intro c
  apply dvd_of_taylor
  intro i hi
  have hcoe : ((taylor (a c) ((fun _ => (1 : F[X])) c - C (v c) * truncN a φ K c *
      ∑ d ∈ range K, C (χ c d) * (C θ⁻¹ * wPoly a) ^ d) : F[X]) : PowerSeries F) =
      1 - PowerSeries.C (v c) * (PowerSeries.trunc K (φ c) : PowerSeries F) *
        ∑ d ∈ range K, PowerSeries.C (χ c d) * (locU a θ c : PowerSeries F) ^ d := by
    simp only [map_sub, taylor_mul, taylor_one, taylor_C, taylor_truncN, map_sum, taylor_pow, locU, map_one]
    rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C,
      coe_sum']
    congr 2
    exact Finset.sum_congr rfl fun d _ => by rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow]
  rw [← Polynomial.coeff_coe, hcoe, map_sub,
    show ∀ A B T : PowerSeries F, A * B * T = B * (A * T) from fun A B T => by ring,
    coeff_trunc_mul_low _ _ K i hi, ← map_sub,
    show ∀ A B T : PowerSeries F, B * (A * T) = A * B * T from fun A B T => by ring]
  exact (PowerSeries.X_pow_dvd_iff).mp (h c) i hi

section Coef
variable (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F)

/-- `zθ_c - a_c` is also a LEFT inverse of `u = w/θ` at `a_c`. -/
lemma locRoot_left (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (c : Fin s) :
    (zθ c - PowerSeries.C (a c)).subst ((locU a θ c : F[X]) : PowerSeries F) = PX := by
  have hunit : IsUnit (PowerSeries.coeff 1 ((locU a θ c : F[X]) : PowerSeries F)) := by
    rw [Polynomial.coeff_coe, coeff_one_locU]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hθ) (wCo_eval_ne a ha c))
  exact PowerSeries.subst_eq_X_of_subst_eq_X _ (constantCoeff_locU a θ c) hunit
    (hasSubst_shift _ _ (hz c).1) (locU_subst a θ zθ hθ hz c)

lemma coeff_one_locRoot_ne (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (c : Fin s) : PowerSeries.coeff 1 (zθ c) ≠ 0 := by
  intro h0
  have := coeff_one_locRoot a θ zθ hθ hz c
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- `v_c = 1/φ_c(a_c)` (the paper's definition in `lem:corrS`). -/
theorem corrV_eq (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) (c : Fin s) :
    corrV zθ g c = (PowerSeries.constantCoeff (locMul a θ g c))⁻¹ := by
  have h1 := coeff_one_locRoot a θ zθ hθ hz c
  rw [corrV, constantCoeff_locMul, mul_inv, ← eq_inv_of_mul_eq_one_left h1, div_eq_mul_inv, mul_comm]

lemma corrV_ne (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F)
    (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (c : Fin s) : corrV zθ g c ≠ 0 :=
  div_ne_zero (coeff_one_locRoot_ne a θ zθ hθ hz c) (hg c)

/-- `χ_{c,0} = 1`. -/
theorem corrCoef_zero (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F)
    (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (c : Fin s) : corrCoef zθ g c 0 = 1 := by
  rw [corrCoef, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv,
    show PowerSeries.constantCoeff (PowerSeries.derivative (zθ c)) = PowerSeries.coeff 1 (zθ c) by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]; simp,
    ← div_eq_mul_inv, ← corrV, div_self (corrV_ne a θ zθ hθ hz g hg c)]

/-- **The correction coefficients of `lem:corrS` are `v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)`**: with `corrV`,
`corrCoef`, `1/φ_c = v_c ∑_{d<K} χ_{c,d} (w/θ)^d + O(w^K)` at `a_c` for every `K` (`φ = locMul a θ g`). -/
theorem corrTruncPS_corrCoef (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ)
    (g : Fin s → PowerSeries F) (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (K : ℕ) :
    CorrTruncPS a θ (locMul a θ g) (corrV zθ g) (corrCoef zθ g) K := by
  intro c
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set U : PowerSeries F := (locU a θ c : PowerSeries F) with hUdef
  set H := PowerSeries.derivative (zθ c) * (g c)⁻¹ with hHdef
  have hU := hasSubst_locU a θ c
  have hd := PowerSeries.derivative_subst (f := zθ c - PowerSeries.C (a c)) hU
  rw [locRoot_left a θ zθ ha hθ hz c, PowerSeries.derivative_X, PowerSeries.derivative_coe] at hd
  have hdZ : PowerSeries.derivative (zθ c - PowerSeries.C (a c)) = PowerSeries.derivative (zθ c) := by simp
  rw [hdZ] at hd
  have hφH : locMul a θ g c * H.subst U = 1 := by
    rw [locMul, hHdef, PowerSeries.subst_mul hU,
      show ∀ A B C D : PowerSeries F, A * B * (C * D) = (A * D) * (C * B) from fun A B C D => by ring,
      ← PowerSeries.subst_mul hU, PowerSeries.mul_inv_cancel _ (hg c), subst_one' _ hU, one_mul, ← hd]
  have hv := corrV_ne a θ zθ hθ hz g hg c
  have hsum : PowerSeries.C (corrV zθ g c) * locMul a θ g c *
      ∑ d ∈ range (K' + 1), PowerSeries.C (corrCoef zθ g c d) * U ^ d =
      locMul a θ g c * (PowerSeries.trunc (K' + 1) H : PowerSeries F).subst U := by
    rw [PowerSeries.subst_coe hU, Polynomial.aeval_eq_sum_range' (PowerSeries.natDegree_trunc_lt H K'),
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [PowerSeries.coeff_trunc, ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_range.mp hd)), Algebra.smul_def, algebraMap_ps, corrCoef,
      show ∀ (x : F) (A B : PowerSeries F), PowerSeries.C (corrV zθ g c) * A * (PowerSeries.C (x / corrV zθ g c) * B)
        = A * (PowerSeries.C (corrV zθ g c * (x / corrV zθ g c)) * B) from fun x A B => by rw [map_mul]; ring,
      mul_div_cancel₀ _ hv]
  set sh : PowerSeries F := PowerSeries.mk fun i ↦ PowerSeries.coeff (i + (K' + 1)) H
  have hsplit := PowerSeries.eq_X_pow_mul_shift_add_trunc (K' + 1) H
  have hHU : H.subst U = U ^ (K' + 1) * sh.subst U + (PowerSeries.trunc (K' + 1) H : PowerSeries F).subst U := by
    conv_lhs => rw [hsplit]
    rw [PowerSeries.subst_add hU, PowerSeries.subst_mul hU, PowerSeries.subst_pow hU, PowerSeries.subst_X hU]
  set κ : PowerSeries F := PowerSeries.mk fun i => PowerSeries.coeff (i + 1) U with hκdef
  have hUX : U = PX * κ := eq_X_mul_shift U (constantCoeff_locU a θ c)
  have hUK : U ^ (K' + 1) = PX ^ (K' + 1) * κ ^ (K' + 1) := by rw [← mul_pow, ← hUX]
  rw [hsum]
  refine ⟨locMul a θ g c * κ ^ (K' + 1) * sh.subst U, ?_⟩
  have h2 : locMul a θ g c * (PowerSeries.trunc (K' + 1) H : PowerSeries F).subst U =
      1 - locMul a θ g c * U ^ (K' + 1) * sh.subst U := by
    rw [← hφH, hHU]; ring
  rw [h2, hUK]
  ring

/-- **The correction data are free parameters of self-similar scrambles**: for every `v` with `v_c ≠ 0` and every
`χ` with `χ_{c,0} = 1` there are unit multipliers `g_c = zθ_c' / (v_c ∑_d χ_{c,d} x^d)` whose self-similar scramble
(the residue form `ssL a θ (locMul a θ g)`, `def:selfsim`) has exactly these `v`, `χ` (`corrV`, `corrCoef`). -/
theorem corr_free (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) :
    ∃ g : Fin s → PowerSeries F, IsSelfSim a θ g (ssL a θ (locMul a θ g)) ∧ corrV zθ g = v ∧
      corrCoef zθ g = χ := by
  set g : Fin s → PowerSeries F := fun c =>
    PowerSeries.derivative (zθ c) * (PowerSeries.C (v c) * PowerSeries.mk (χ c))⁻¹ with hgdef
  have hd1 : ∀ c, PowerSeries.constantCoeff (PowerSeries.derivative (zθ c)) = PowerSeries.coeff 1 (zθ c) :=
    fun c => by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]; simp
  have hm0 : ∀ c, PowerSeries.constantCoeff (PowerSeries.C (v c) * PowerSeries.mk (χ c)) = v c := fun c => by
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, hχ0, mul_one]
  have hg0 : ∀ c, PowerSeries.constantCoeff (g c) = PowerSeries.coeff 1 (zθ c) * (v c)⁻¹ := fun c => by
    rw [hgdef, map_mul, PowerSeries.constantCoeff_inv, hd1, hm0]
  have hgu : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0 := fun c => by
    rw [hg0]; exact mul_ne_zero (coeff_one_locRoot_ne a θ zθ hθ hz c) (inv_ne_zero (hv c))
  have hV : corrV zθ g = v := by
    funext c; rw [corrV, hg0, div_mul_eq_div_div, div_self (coeff_one_locRoot_ne a θ zθ hθ hz c), one_div, inv_inv]
  refine ⟨g, ?_, hV, ?_⟩
  · have h := ssL_selfsim a θ ha hθ zθ hz (locMul a θ g) (fun c => by
      rw [constantCoeff_locMul]; exact mul_ne_zero (hgu c) (mul_ne_zero (inv_ne_zero hθ) (wCo_eval_ne a ha c)))
    rwa [ssMul_locMul a θ zθ hθ hz] at h
  · funext c d
    have hH : PowerSeries.derivative (zθ c) * (g c)⁻¹ = PowerSeries.C (v c) * PowerSeries.mk (χ c) := by
      have hB : PowerSeries.constantCoeff (PowerSeries.C (v c) * PowerSeries.mk (χ c)) ≠ 0 := by rw [hm0]; exact hv c
      have hinv : (PowerSeries.C (v c) * PowerSeries.mk (χ c))⁻¹⁻¹ = PowerSeries.C (v c) * PowerSeries.mk (χ c) :=
        ((PowerSeries.eq_inv_iff_mul_eq_one (by rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hB)).mpr
          (PowerSeries.mul_inv_cancel _ hB)).symm
      rw [hgdef, PowerSeries.mul_inv_rev, hinv, ← mul_assoc, mul_right_comm,
        PowerSeries.mul_inv_cancel _ (by rw [hd1]; exact coeff_one_locRoot_ne a θ zθ hθ hz c), one_mul]
    rw [corrCoef, hH, hV, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_div_cancel_left₀ _ (hv c)]

/-- **Uniqueness**: the correction data `(v, χ)` determine the multipliers of a self-similar scramble. -/
theorem corr_inj (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g g' : Fin s → PowerSeries F)
    (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (hg' : ∀ c, PowerSeries.constantCoeff (g' c) ≠ 0)
    (hv : corrV zθ g = corrV zθ g') (hχ : corrCoef zθ g = corrCoef zθ g') : g = g' := by
  funext c
  have hH : PowerSeries.derivative (zθ c) * (g c)⁻¹ = PowerSeries.derivative (zθ c) * (g' c)⁻¹ := by
    ext d
    have h := congrFun (congrFun hχ c) d
    rw [corrCoef, corrCoef, hv] at h
    exact (div_left_inj' (corrV_ne a θ zθ hθ hz g' hg' c)).mp h
  have hd0 : PowerSeries.constantCoeff (PowerSeries.derivative (zθ c)) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simpa using coeff_one_locRoot_ne a θ zθ hθ hz c
  have hne : PowerSeries.derivative (zθ c) * (g c)⁻¹ ≠ 0 := fun h0 => by
    have := congrArg PowerSeries.constantCoeff h0
    rw [map_mul, PowerSeries.constantCoeff_inv, map_zero] at this
    exact mul_ne_zero hd0 (inv_ne_zero (hg c)) this
  apply mul_left_cancel₀ hne
  conv_rhs => rw [hH]
  rw [mul_assoc, mul_assoc, PowerSeries.inv_mul_cancel _ (hg c), PowerSeries.inv_mul_cancel _ (hg' c)]

end Coef

section Bridge
variable (a : Fin s → F) (θ : F)

/-- **`lem:corrS` for `def:selfsim` as written, any correction data**: if `v`, `χ` (`χ_{c,0} = 1`) are correction
coefficients of the local multipliers `φ = locMul a θ g` up to order `K` (`CorrTruncPS`), every point of `P_{sK-1}`
satisfies `∑_c v_c [y_{c,K-1} + ∑_{d=1}^{K-1} χ_{c,d} y_{c,K-1-d}] = 0`. -/
theorem selfsim_corr_of {q : ℕ} [NeZero q] (D : DigitCode F q) (hs : 2 ≤ s) (ha : Function.Injective a)
    (hθ : θ ≠ 0) (g : Fin s → PowerSeries F) (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L)
    (v : Fin s → F) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTruncPS a θ (locMul a θ g) v χ K) : CorrRel D (scrGen a L) v χ K := by
  rw [selfsim_scrGen a θ ha hθ g L hL,
    corrRel_congr D _ (ssResGen a θ (truncN a (locMul a θ g) K) (fun _ => 1)) v χ K hK
      (fun c n k hn => (ssResGen_truncN a ha θ _ K c n k hn).symm)]
  exact ssRes_corr_seq D hs a ha θ hθ _ _ (fun c => by simp) v χ hχ0 K hK (corrTrunc_of_PS a θ _ v χ K htr)

/-- **`lem:corrS` for `def:selfsim` as written** (unconditional): every self-similar scramble with scale `θ`,
unit multipliers `g_c` and scaled local roots `zθ` satisfies, for every `K ≥ 1`, the corrected skeleton relation on
`P_{sK-1}` with `v_c = 1/φ_c(a_c)` (`corrV_eq`) and the correction coefficients `χ_{c,d}` of the expansion
`1/φ_c = v_c ∑_d χ_{c,d} (w/θ)^d`, i.e. `v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)` (`corrCoef`). -/
theorem selfsim_corrS {q : ℕ} [NeZero q] (D : DigitCode F q) (hs : 2 ≤ s) (ha : Function.Injective a)
    (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (K : ℕ) (hK : 1 ≤ K) :
    CorrRel D (scrGen a L) (corrV zθ g) (corrCoef zθ g) K :=
  selfsim_corr_of a θ D hs ha hθ g L hL _ _ (corrCoef_zero a θ zθ hθ hz g hL.1) K hK
    (corrTruncPS_corrCoef a θ zθ ha hθ hz g hL.1 K)

lemma selfsim_rows (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (K : ℕ) :
    ∀ c n k, n ≤ K + 0 → scrGen a L c n k = ssResGen a θ (truncN a (locMul a θ g) (K + 1)) (fun _ => 1) c n k :=
  fun c n k hn => by
    rw [selfsim_scrGen a θ ha hθ g L hL, ssResGen_truncN a ha θ _ (K + 1) c n k (by omega)]

/-- **`prop:joint`(i) for `def:selfsim` as written**: at every full level `K ≥ 1`, for every step `e` and carry
lengths `l_c ∈ [0, K]`, the changes `σ_c = ∑_{c'} e_{c'} D(l_{c'})[c][c']` of the geometric digits satisfy
`∑_c v_c σ_c = -∑_c e_c v_c Ψ_c(l_c)` (`v = corrV`, `χ = corrCoef`, `Ψ_c(j) = ∑_{d=1}^j χ_{c,d}`). -/
theorem selfsim_joint_step (hs : 2 ≤ s) (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L)
    (K : ℕ) (hK : 1 ≤ K) (e : Fin s → ℤ) (lc : Fin s → ℕ) (hl : ∀ c, lc c ≤ K) (Dr : Fin s → Fin s → F)
    (hD : ∀ c c', IsCarryEntry (scrGen a L) K 0 (lc c') c c' (Dr c c')) :
    ∑ c, corrV zθ g c * ∑ c', (e c' : F) * Dr c c' =
      -∑ c, (e c : F) * (corrV zθ g c * psiSum (corrCoef zθ g) c (lc c)) :=
  joint_step hs a ha θ hθ _ (fun _ => 1) (fun c => by simp) (corrV zθ g) (corrCoef zθ g)
    (corrCoef_zero a θ zθ hθ hz g hL.1) K hK
    (corrTrunc_of_PS a θ _ _ _ (K + 1) (corrTruncPS_corrCoef a θ zθ ha hθ hz g hL.1 (K + 1))) e lc hl Dr
    (fun c c' => (carry_congr _ _ K 0 _ c c' _ (selfsim_rows a θ ha hθ g L hL K)).mp (hD c c'))

/-- **`prop:joint`(ii) for `def:selfsim` as written**: two self-similar scrambles (scale `θ`, the same local roots)
whose multipliers differ only in coordinate `c`, with the same `v_c` and the same correction coefficients
`χ_{c,d}`, `d < l`, have at every full level `K ≥ l ≥ 1` the same cross responses `X^{(l)}_{c₁←c}` and the same
`O^{(l)}_c + Ψ_c(l)` (carry length `l` in coordinate `c`). -/
theorem selfsim_joint_ii (hs : 2 ≤ s) (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (g g' : Fin s → PowerSeries F) (L L' : Fin s → ℕ → ℕ → F)
    (hL : IsSelfSim a θ g L) (hL' : IsSelfSim a θ g' L') (c : Fin s) (hg' : ∀ c', c' ≠ c → g' c' = g c')
    (hv : corrV zθ g' c = corrV zθ g c) (K : ℕ) (hK : 1 ≤ K) (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K)
    (hχ : ∀ d, d < l → corrCoef zθ g' c d = corrCoef zθ g c d) (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (scrGen a L) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (scrGen a L') K 0 l c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧
      Dnew c + psiSum (corrCoef zθ g') c l = Dold c + psiSum (corrCoef zθ g) c l := by
  have hvv : corrV zθ g' = corrV zθ g := by
    funext c'
    by_cases h : c' = c
    · subst h; exact hv
    · simp only [corrV, hg' c' h]
  have htr' := corrTrunc_of_PS a θ _ _ _ (K + 1) (corrTruncPS_corrCoef a θ zθ ha hθ hz g' hL'.1 (K + 1))
  rw [hvv] at htr'
  refine joint_ii hs a ha θ hθ _ (fun _ => 1) _ (fun _ => 1) c (fun c' h => ?_) (fun _ _ => rfl)
    (fun c => by simp) (by simp) ?_ (corrV zθ g) (corrV_ne a θ zθ hθ hz g hL.1 c) (corrCoef zθ g) (corrCoef zθ g')
    (corrCoef_zero a θ zθ hθ hz g hL.1) (corrCoef_zero a θ zθ hθ hz g' hL'.1) K hK
    (corrTrunc_of_PS a θ _ _ _ (K + 1) (corrTruncPS_corrCoef a θ zθ ha hθ hz g hL.1 (K + 1))) htr' l hl hlK hχ
    Dold Dnew (fun c₁ => (carry_congr _ _ K 0 _ c₁ c _ (selfsim_rows a θ ha hθ g L hL K)).mp (hold c₁))
    (fun c₁ => (carry_congr _ _ K 0 _ c₁ c _ (selfsim_rows a θ ha hθ g' L' hL' K)).mp (hnew c₁))
  · simp only [truncN, locMul, hg' c' h]
  · rw [eval_truncN a _ (K + 1) (by omega)]
    exact selfsim_locMul_unit a θ ha hθ g' L' hL' c

end Bridge

end GeoSeq
