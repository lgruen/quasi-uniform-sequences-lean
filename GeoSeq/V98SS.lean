/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Cor

@[expose] public section

/-!
# GeoSeq stage V9-8 (part 5): self-similar scrambles in residue form (`prop:onerel`, `cor:residuerows`)

Self-similar scrambles are taken in the residue form of `lem:resform`(b) (right-hand side): local multipliers
`φ_c ∈ F[[t]]` (units, `t = z - a_c`), `y_{c,n}(V) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz)` (`ssL`). The equivalence with
`def:selfsim` (`lem:resform`(b), which needs `lem:reschange` in characteristic `p`) is NOT formalized.

* `ssL_digit` (the residue reading), `ssL_scramble` (a scramble of the frame).
* **`onerel_poly`** (`prop:onerel`(i), polynomial part, and (ii)): a level-independent relation valid on the
  prefixes `P_{sT+i}` for all `T ≥ T₀` has a polynomial `A ≠ 0`, `deg A < s - i`, with `φ_c ϑ_c(w/θ) = A` as power
  series at every place (`ϑpoly c = ϑ_c(w/θ)`).
* **`onerel_skel`** (`prop:onerel`(iii), skeleton part): a skeleton relation `∑_c v_c y_{c,T} = 0` on `P_{s(T+1)-1}` for
  all `T ≥ T₀` forces `φ_c = α/v_c` (constants) and the scramble is the residue sequence `𝓡_{v/α}` (`ssL = resL`);
  **`onerel_stag`** (`prop:onerel`(iii), staggered part): `y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` for all
  `T ≥ T₀` forces every `k_c ≠ 0`, `φ_{c⋆} = λ w_{c⋆}` and `φ_c (z - a_{c⋆}) = -λθ/k_c`, i.e. the local multipliers
  of `𝓡^⋆` with `μ⋆ = λθ`, and then `ssL = resStarL` (`onerel_stag_gen`).
* **`residuerows_ss`** (`cor:residuerows`, self-similar clause): residue rows at every level `n ≥ n₀` force
  constant local multipliers, i.e. the residue sequence.
-/

namespace GeoSeq

open Finset Polynomial

section SS
variable {F : Type*} [Field F] {s : ℕ}

local notation "tw" a:max c:max => ((taylor (a c) (wCo a c) : F[X]) : PowerSeries F)

/-- The residue reading of a self-similar scramble: `y_{c,n}(V) = θ^{n+1} [t^n] V(a_c+t) φ_c w_c(a_c+t)^{-n-1}`. -/
theorem ssL_digit (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (c : Fin s) (n : ℕ) (V : F[X]) :
    frDigit a (ssL a θ φ) c n V =
      θ ^ (n + 1) * PowerSeries.coeff n (((taylor (a c) V : F[X]) : PowerSeries F) *
        (φ c * ((tw a c)⁻¹) ^ (n + 1))) := by
  rw [frDigit, coeff_mul_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ssL, Polynomial.coeff_coe]; ring

/-- A self-similar scramble in residue form is a scramble of the frame (`θ ≠ 0`, unit local multipliers). -/
theorem ssL_scramble (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (φ : Fin s → PowerSeries F)
    (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) : IsScramble (ssL a θ φ) := by
  intro c n
  rw [ssL, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
    PowerSeries.constantCoeff_inv, constantCoeff_taylor]
  exact mul_ne_zero (pow_ne_zero _ hθ) (mul_ne_zero (hφ c) (pow_ne_zero _ (inv_ne_zero (wCo_eval_ne a ha c))))

/-- Coefficient extraction: if `[t^T] V(a+t) Y u = 0` for every polynomial `V`, with `u` a unit, then
`[t^j] Y = 0` for `j ≤ T`. -/
theorem ps_coeff_zero (b : F) (T : ℕ) (Y u : PowerSeries F) (hu : PowerSeries.constantCoeff u ≠ 0)
    (h : ∀ V : F[X], PowerSeries.coeff T (((taylor b V : F[X]) : PowerSeries F) * Y * u) = 0) :
    ∀ j ≤ T, PowerSeries.coeff j Y = 0 := by
  have h1 : ∀ j ≤ T, PowerSeries.coeff j (Y * u) = 0 := by
    intro j hj
    have := h ((X - C b) ^ (T - j))
    rwa [taylor_pow, taylor_X_sub_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
      PowerSeries.coeff_X_pow_mul', if_pos (by omega), show T - (T - j) = j by omega] at this
  intro j hj
  have e : Y = (Y * u) * u⁻¹ := by rw [mul_assoc, PowerSeries.mul_inv_cancel _ hu, mul_one]
  rw [e, coeff_mul_range]
  exact Finset.sum_eq_zero fun k hk => by rw [h1 k (by simp at hk; omega), zero_mul]

lemma coe_sum' {ι : Type*} (t : Finset ι) (g : ι → F[X]) :
    ((∑ i ∈ t, g i : F[X]) : PowerSeries F) = ∑ i ∈ t, (g i : PowerSeries F) :=
  map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) g t

lemma taylor_wPoly (a : Fin s → F) (c : Fin s) :
    ((taylor (a c) (wPoly a) : F[X]) : PowerSeries F) = PowerSeries.X * tw a c := by
  rw [wPoly_eq a c, taylor_mul, taylor_X_sub_C, Polynomial.coe_mul, Polynomial.coe_X]

lemma liEmbed_sum (J T : ℕ) (hJT : J ≤ T) (ϑ : Fin s → ℕ → F) (c : Fin s) (g : ℕ → F) :
    ∑ n ∈ range (T + 1), liEmbed J T ϑ c n * g n = ∑ i ∈ range (J + 1), ϑ c i * g (T - i) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show T - J ≤ T + 1 by omega),
    Finset.sum_eq_zero (s := range (T - J)) fun n hn => by
      simp only [liEmbed]; rw [if_neg (by simp at hn; omega), zero_mul],
    zero_add, Finset.sum_Ico_eq_sum_range, show T + 1 - (T - J) = J + 1 by omega, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp only [liEmbed]
  rw [if_pos ⟨by omega, by omega⟩, show T - (T - J + (J + 1 - 1 - i)) = i by omega,
    show T - J + (J + 1 - 1 - i) = T - i by omega]

/-- The relation form of a level-independent family at level `T`, place by place:
`∑_{i ≤ J} ϑ_{c,i} y_{c,T-i}(V) = θ^{T+1} [t^T] V(a_c+t) φ_c ϑ_c(w/θ)(a_c+t) w_c(a_c+t)^{-T-1}`. -/
theorem ss_place (a : Fin s → F) (θ : F) (hθ : θ ≠ 0) (φ : Fin s → PowerSeries F) (ha : Function.Injective a)
    (J T : ℕ) (hJT : J ≤ T) (ϑ : Fin s → ℕ → F) (c : Fin s) (V : F[X]) :
    ∑ n ∈ range (T + 1), liEmbed J T ϑ c n * frDigit a (ssL a θ φ) c n V =
      θ ^ (T + 1) * PowerSeries.coeff T (((taylor (a c) V : F[X]) : PowerSeries F) *
        (φ c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F)) * ((tw a c)⁻¹) ^ (T + 1)) := by
  have hu : tw a c * (tw a c)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_taylor]; exact wCo_eval_ne a ha c)
  rw [liEmbed_sum J T hJT, ϑpoly, map_sum, coe_sum', Finset.mul_sum, Finset.mul_sum,
    Finset.sum_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ T := by have := Finset.mem_range.mp hi; omega
  rw [ssL_digit, taylor_mul, taylor_C, taylor_pow, taylor_mul, taylor_C, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_C, taylor_wPoly]
  have e : ((taylor (a c) V : F[X]) : PowerSeries F) * (φ c * (PowerSeries.C (ϑ c i) *
      (PowerSeries.C θ⁻¹ * (PowerSeries.X * tw a c)) ^ i)) * ((tw a c)⁻¹) ^ (T + 1) =
      PowerSeries.C (ϑ c i * θ⁻¹ ^ i) * (PowerSeries.X ^ i *
        (((taylor (a c) V : F[X]) : PowerSeries F) * (φ c * ((tw a c)⁻¹) ^ (T - i + 1)))) := by
    rw [show T + 1 = (T - i + 1) + i by omega, pow_add]
    have : (tw a c) ^ i * ((tw a c)⁻¹) ^ i = 1 := by rw [← mul_pow, hu, one_pow]
    simp only [mul_pow, map_mul, map_pow]
    linear_combination (((taylor (a c) V : F[X]) : PowerSeries F) * φ c * PowerSeries.C (ϑ c i) *
      PowerSeries.C θ⁻¹ ^ i * PowerSeries.X ^ i * ((tw a c)⁻¹) ^ (T - i + 1)) * this
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos hi',
    show T + 1 = (T - i + 1) + i by omega, pow_add]
  have hθi : θ ^ i * θ⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hθ, one_pow]
  linear_combination (-ϑ c i * θ ^ (T - i + 1) * PowerSeries.coeff (T - i)
    (((taylor (a c) V : F[X]) : PowerSeries F) * (φ c * ((tw a c)⁻¹) ^ (T - i + 1)))) * hθi

lemma locRes_ps (b : F) (k : ℕ) (V A U : F[X]) :
    locRes b (k + 1) (V * A) (U ^ (k + 1)) = PowerSeries.coeff k (((taylor b V : F[X]) : PowerSeries F) *
      ((taylor b A : F[X]) : PowerSeries F) * ((((taylor b U : F[X]) : PowerSeries F))⁻¹) ^ (k + 1)) := by
  rw [locRes, if_neg (by omega), Nat.add_sub_cancel, taylor_mul, taylor_pow, Polynomial.coe_mul,
    Polynomial.coe_pow, ps_inv_pow]

/-- A polynomial whose Taylor coefficients vanish up to `T` at every place is divisible by `w^{T+1}`. -/
lemma wPoly_pow_dvd (a : Fin s → F) (ha : Function.Injective a) (T : ℕ) (D : F[X])
    (h : ∀ c, ∀ j ≤ T, (taylor (a c) D).coeff j = 0) : wPoly a ^ (T + 1) ∣ D := by
  rw [wPoly, ← Finset.prod_pow]
  refine Finset.prod_dvd_of_coprime (fun c _ c' _ hcc' => ((pairwise_coprime_X_sub_C ha) hcc').pow) fun c _ => ?_
  rw [X_sub_C_pow_dvd_iff]; exact fun j hj => h c j (by omega)

/-- **`prop:onerel`(i) (polynomial part) and (ii).** Let a self-similar scramble (residue form, `θ ≠ 0`, unit local
multipliers) satisfy the level-independent relation `∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i} = 0` on the prefixes
`P_{sT+i}` for every `T ≥ T₀ ≥ J` (`i = 0`: on the full levels). Then there is a polynomial `A ≠ 0` with
`deg A < s - i` and `φ_c · ϑ_c(w/θ) = A` as power series at every place `a_c`. -/
theorem onerel_poly (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) (J T₀ i : ℕ) (hJ : J ≤ T₀)
    (ϑ : Fin s → ℕ → F) (hsupp : ∀ c i, J < i → ϑ c i = 0) (hϑ0 : ϑ ≠ 0)
    (hrel : ∀ T, T₀ ≤ T → liEmbed J T ϑ ∈ relSpace a (ssL a θ φ) T (s * T + i)) :
    ∃ A : F[X], A ≠ 0 ∧ A.degree < ((s - i : ℕ) : WithBot ℕ) ∧
      ∀ c, φ c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F) = ((taylor (a c) A : F[X]) : PowerSeries F) := by
  set L := ssL a θ φ
  have hL : IsScramble L := ssL_scramble a ha θ hθ φ hφ
  have hfs : ∀ T, ∀ c n, T < n → liEmbed J T ϑ c n = 0 := fun T c n h => by
    simp only [liEmbed]; rw [if_neg (by omega)]
  set At : ℕ → F[X] := fun T => C ((θ ^ (T + 1))⁻¹) * relPoly a L (liEmbed J T ϑ) T with hAt
  have hdeg : ∀ T, T₀ ≤ T → (At T).degree < ((s - i : ℕ) : WithBot ℕ) := by
    intro T hT
    have := relPoly_degree_lt a ha L _ T _ (hrel T hT)
    rw [show s * (T + 1) - (s * T + i) = s - i by rw [Nat.mul_succ]; omega] at this
    rw [hAt, degree_C_mul (inv_ne_zero (pow_ne_zero _ hθ))]; exact this
  have hne : ∀ T, T₀ ≤ T → At T ≠ 0 := by
    intro T hT h0
    rw [hAt, mul_eq_zero, C_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact inv_ne_zero (pow_ne_zero _ hθ) h0
    · exact hϑ0 (liEmbed_inj J T (by omega) ϑ hsupp
        ((relPoly_eq_zero_iff a ha L hL _ T (hfs T)).mp h0))
  have hcong : ∀ T, T₀ ≤ T → ∀ c, ∀ j ≤ T, PowerSeries.coeff j (φ c *
      ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F)) = (taylor (a c) (At T)).coeff j := by
    intro T hT c
    set Y := PowerSeries.C (θ ^ (T + 1)) * (φ c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F)) -
      ((taylor (a c) (relPoly a L (liEmbed J T ϑ) T) : F[X]) : PowerSeries F)
    have hY := ps_coeff_zero (a c) T Y (((tw a c)⁻¹) ^ (T + 1))
      (by rw [map_pow, PowerSeries.constantCoeff_inv, constantCoeff_taylor]
          exact pow_ne_zero _ (inv_ne_zero (wCo_eval_ne a ha c))) (fun V => by
        have h1 := ss_place a θ hθ φ ha J T (by omega) ϑ c V
        rw [place_eq, place_eq_locRes a ha, locRes_ps] at h1
        rw [show ((taylor (a c) V : F[X]) : PowerSeries F) * Y * ((tw a c)⁻¹) ^ (T + 1) =
            PowerSeries.C (θ ^ (T + 1)) * (((taylor (a c) V : F[X]) : PowerSeries F) *
              (φ c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F)) * ((tw a c)⁻¹) ^ (T + 1)) -
            ((taylor (a c) V : F[X]) : PowerSeries F) *
              ((taylor (a c) (relPoly a L (liEmbed J T ϑ) T) : F[X]) : PowerSeries F) * ((tw a c)⁻¹) ^ (T + 1) by
            simp only [Y]; ring, map_sub, PowerSeries.coeff_C_mul, ← h1, sub_self])
    intro j hj
    have := hY j hj
    simp only [Y, map_sub, PowerSeries.coeff_C_mul, Polynomial.coeff_coe, sub_eq_zero] at this
    rw [hAt, taylor_mul, taylor_C, coeff_C_mul, ← this, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hθ), one_mul]
  have hstep : ∀ T, T₀ ≤ T → At (T + 1) = At T := by
    intro T hT
    have hdvd := wPoly_pow_dvd a ha T (At (T + 1) - At T) fun c j hj => by
      rw [map_sub, coeff_sub, ← hcong (T + 1) (by omega) c j (by omega), ← hcong T hT c j hj, sub_self]
    refine sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdvd ?_)
    rw [degree_eq_natDegree (pow_ne_zero _ (wPoly_monic a).ne_zero), natDegree_pow, natDegree_wPoly]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ((hdeg _ (by omega)).trans_le ?_) ((hdeg _ hT).trans_le ?_))
    all_goals
      exact_mod_cast (show s - i ≤ (T + 1) * s by
        calc s - i ≤ s := Nat.sub_le _ _
          _ ≤ (T + 1) * s := Nat.le_mul_of_pos_left _ (by omega))
  have hconst : ∀ T, T₀ ≤ T → At T = At T₀ := by
    intro T hT
    induction T, hT using Nat.le_induction with
    | base => rfl
    | succ T hT ih => rw [hstep T hT, ih]
  refine ⟨At T₀, hne T₀ le_rfl, hdeg T₀ le_rfl, fun c => PowerSeries.ext fun j => ?_⟩
  rw [hcong (max T₀ j) (le_max_left _ _) c j (le_max_right _ _), hconst _ (le_max_left _ _),
    Polynomial.coeff_coe]

/-- Constant local multipliers give the residue sequence: `ssL a θ (C ∘ β) = resL a θ β⁻¹`. -/
theorem ssL_const (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (β : Fin s → F)
    (hφ : ∀ c, φ c = PowerSeries.C (β c)) : ssL a θ φ = resL a θ (fun c => (β c)⁻¹) := by
  funext c n k
  rw [ssL, resL, hφ c, PowerSeries.coeff_C_mul, inv_inv]; ring

lemma taylor_eq_zero (b : F) (A : F[X]) (h : taylor b A = 0) : A = 0 := by
  have := congrArg (taylor (-b)) h
  rwa [taylor_neg_taylor, map_zero] at this

/-- **`prop:onerel`(iii), skeleton part.** If a self-similar scramble (residue form) satisfies a skeleton relation
`∑_c v_c y_{c,T} = 0` on `P_{s(T+1)-1}` for every `T ≥ T₀`, `v ≠ 0`, then every `v_c ≠ 0`, `φ_c = α/v_c` for one
`α ≠ 0`, and the scramble is the residue sequence with scale `θ` and check vector `v/α ∝ v` (`ssL = resL`). -/
theorem onerel_skel (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) (T₀ : ℕ) (v : Fin s → F)
    (hv : v ≠ 0) (hrel : ∀ T, T₀ ≤ T → skelVec T v ∈ relSpace a (ssL a θ φ) T (s * (T + 1) - 1)) :
    ∃ α : F, α ≠ 0 ∧ (∀ c, v c ≠ 0 ∧ φ c = PowerSeries.C (α / v c)) ∧
      ssL a θ φ = resL a θ (fun c => v c / α) := by
  have hs1 : 1 ≤ s := by
    by_contra h; rw [not_le] at h; apply hv; funext c; exact absurd c.2 (by omega)
  set ϑ : Fin s → ℕ → F := fun c i => if i = 0 then v c else 0
  have hemb : ∀ T, liEmbed 0 T ϑ = skelVec T v := fun T => by
    funext c n; simp only [liEmbed, skelVec, ϑ]
    by_cases h : n = T
    · subst h; simp
    · rw [if_neg (by omega), if_neg h]
  have hϑ0 : ϑ ≠ 0 := fun h => hv (funext fun c => by have := congrFun (congrFun h c) 0; simpa [ϑ] using this)
  obtain ⟨A, hA0, hAdeg, hid⟩ := onerel_poly a ha θ hθ φ hφ 0 T₀ (s - 1) (Nat.zero_le _) ϑ
    (fun c i hi => by simp [ϑ, show i ≠ 0 by omega]) hϑ0
    (fun T hT => by rw [hemb, show s * T + (s - 1) = s * (T + 1) - 1 by rw [Nat.mul_succ]; omega]; exact hrel T hT)
  rw [show s - (s - 1) = 1 by omega] at hAdeg
  have hAC : A = C (A.coeff 0) := eq_C_of_degree_le_zero (by exact_mod_cast Order.le_of_lt_succ hAdeg)
  set α := A.coeff 0
  have hα : α ≠ 0 := fun h => hA0 (by rw [hAC, h, map_zero])
  have hpoly : ∀ c, ϑpoly a θ 0 ϑ c = C (v c) := fun c => by simp [ϑpoly, ϑ]
  have key : ∀ c, φ c * PowerSeries.C (v c) = PowerSeries.C α := fun c => by
    have := hid c
    rwa [hpoly, taylor_C, hAC, taylor_C, Polynomial.coe_C, Polynomial.coe_C] at this
  have hvc : ∀ c, v c ≠ 0 := fun c h => by
    have := key c; rw [h, map_zero, mul_zero] at this
    exact hα (PowerSeries.C_injective (this.symm.trans (map_zero _).symm))
  have hφc : ∀ c, φ c = PowerSeries.C (α / v c) := fun c => by
    have e : φ c = φ c * PowerSeries.C (v c) * PowerSeries.C (v c)⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ (hvc c), map_one, mul_one]
    rw [e, key, ← map_mul, div_eq_mul_inv]
  refine ⟨α, hα, fun c => ⟨hvc c, hφc c⟩, ?_⟩
  rw [ssL_const a θ φ (fun c => α / v c) hφc]
  funext c n k; simp only [inv_div]

/-- **`cor:residuerows`, self-similar clause.** If a self-similar scramble (residue form) has residue rows up to
scalars, `y_{c,n} = μ_{c,n} ŷ_{c,n}`, at every level `n ≥ n₀`, then its local multipliers are constants and it is the
residue sequence `𝓡_v` with `v_c = φ_c(0)^{-1}`. -/
theorem residuerows_ss (a : Fin s → F) (θ : F) (hθ : θ ≠ 0) (ha : Function.Injective a)
    (φ : Fin s → PowerSeries F) (n₀ : ℕ)
    (hrow : ∀ n, n₀ ≤ n → ∃ μ : Fin s → F, ∀ c V, frDigit a (ssL a θ φ) c n V = μ c * resDig a c n V) :
    ssL a θ φ = resL a θ (fun c => (PowerSeries.constantCoeff (φ c))⁻¹) := by
  refine ssL_const a θ φ _ fun c => PowerSeries.ext fun j => ?_
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  · rw [PowerSeries.coeff_C, if_neg (by omega)]
    obtain ⟨μ, hμ⟩ := hrow (max n₀ j) (le_max_left _ _)
    set n := max n₀ j
    have hY := ps_coeff_zero (a c) n (PowerSeries.C (θ ^ (n + 1)) * φ c - PowerSeries.C (μ c))
      (((tw a c)⁻¹) ^ (n + 1))
      (by rw [map_pow, PowerSeries.constantCoeff_inv, constantCoeff_taylor]
          exact pow_ne_zero _ (inv_ne_zero (wCo_eval_ne a ha c))) (fun V => by
        have h1 := hμ c V
        have e := locRes_ps (a c) n V 1 (wCo a c)
        rw [mul_one, taylor_one, map_one, Polynomial.coe_one, mul_one] at e
        rw [ssL_digit, resDig, e] at h1
        rw [show ((taylor (a c) V : F[X]) : PowerSeries F) * (PowerSeries.C (θ ^ (n + 1)) * φ c -
            PowerSeries.C (μ c)) * ((tw a c)⁻¹) ^ (n + 1) =
            PowerSeries.C (θ ^ (n + 1)) * (((taylor (a c) V : F[X]) : PowerSeries F) *
              (φ c * ((tw a c)⁻¹) ^ (n + 1))) -
            PowerSeries.C (μ c) * (((taylor (a c) V : F[X]) : PowerSeries F) * ((tw a c)⁻¹) ^ (n + 1)) by ring,
          map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, h1, sub_self])
    have := hY j (le_max_right _ _)
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C, if_neg (by omega), sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hθ)

/-- **`prop:onerel`(iii), staggered part.** If a self-similar scramble (residue form) satisfies
`y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` for every `T ≥ T₀ ≥ 1` (`s ≥ 2`), then every `k_c ≠ 0` and, for one
`λ ≠ 0`, `φ_{c⋆} = λ w_{c⋆}` and `φ_c (z - a_{c⋆}) = -λθ/k_c` (`c ≠ c⋆`) as power series: the local multipliers of the
staggered residue sequence with `μ⋆ = λθ`, `μ_c = -μ⋆/k_c` (`onerel_stag_gen`). -/
theorem onerel_stag (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) (hs : 2 ≤ s) (T₀ : ℕ)
    (hT₀ : 1 ≤ T₀) (cs : Fin s) (k : Fin s → F)
    (hrel : ∀ T, T₀ ≤ T → stagVec cs k T ∈ relSpace a (ssL a θ φ) T (s * T)) :
    (∀ c, c ≠ cs → k c ≠ 0) ∧ ∃ lam : F, lam ≠ 0 ∧ φ cs = PowerSeries.C lam * tw a cs ∧
      ∀ c, c ≠ cs → φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) =
        PowerSeries.C (-(lam * θ) / k c) := by
  set ϑ : Fin s → ℕ → F := fun c i => if c = cs then (if i = 0 then 1 else 0) else (if i = 1 then -k c else 0)
  have hemb : ∀ T, 1 ≤ T → liEmbed 1 T ϑ = stagVec cs k T := fun T hT => by
    funext c n
    simp only [liEmbed, stagVec, ϑ]
    by_cases hc : c = cs
    · simp only [hc, if_true]
      by_cases hn : n = T
      · subst hn; simp
      · by_cases hb : n ≤ T ∧ T ≤ n + 1
        · rw [if_pos hb, if_neg (by omega : T - n ≠ 0), if_neg hn]
        · rw [if_neg hb, if_neg hn]
    · simp only [hc, if_false]
      by_cases hn : n + 1 = T
      · rw [if_pos ⟨by omega, by omega⟩, if_pos (by omega : T - n = 1), if_pos hn]
      · by_cases hb : n ≤ T ∧ T ≤ n + 1
        · rw [if_pos hb, if_neg (by omega : T - n ≠ 1), if_neg hn]
        · rw [if_neg hb, if_neg hn]
  have hϑ0 : ϑ ≠ 0 := fun h => by have := congrFun (congrFun h cs) 0; simp [ϑ] at this
  obtain ⟨A, hA0, hAdeg, hid⟩ := onerel_poly a ha θ hθ φ hφ 1 T₀ 0 hT₀ ϑ
    (fun c i hi => by simp only [ϑ]; split_ifs <;> first | rfl | omega)
    hϑ0 (fun T hT => by rw [hemb T (by omega), add_zero]; exact hrel T hT)
  rw [Nat.sub_zero] at hAdeg
  have hpcs : ϑpoly a θ 1 ϑ cs = 1 := by simp [ϑpoly, ϑ]
  have hpc : ∀ c, c ≠ cs → ϑpoly a θ 1 ϑ c = C (-k c) * (C θ⁻¹ * wPoly a) := fun c hc => by
    simp [ϑpoly, ϑ, Finset.sum_range_succ, hc]
  have hidc : ∀ c, c ≠ cs → φ c * (PowerSeries.C (-k c) * (PowerSeries.C θ⁻¹ * (PowerSeries.X * tw a c))) =
      ((taylor (a c) A : F[X]) : PowerSeries F) := fun c hc => by
    have := hid c
    rwa [hpc c hc, taylor_mul, taylor_C, taylor_mul, taylor_C, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_C, taylor_wPoly] at this
  have hroot : ∀ c, c ≠ cs → A.eval (a c) = 0 := fun c hc => by
    have := congrArg PowerSeries.constantCoeff (hidc c hc)
    simpa [constantCoeff_taylor] using this.symm
  have hk : ∀ c, c ≠ cs → k c ≠ 0 := fun c hc h0 => by
    have := hidc c hc
    rw [h0, neg_zero, map_zero, zero_mul, mul_zero] at this
    exact hA0 (taylor_eq_zero (a c) A (Polynomial.coe_eq_zero_iff.mp this.symm))
  have hdvd : wCo a cs ∣ A := by
    rw [wCo]
    refine Finset.prod_dvd_of_coprime (fun c _ c' _ hcc' => (pairwise_coprime_X_sub_C ha) hcc') fun c hc => ?_
    exact dvd_iff_isRoot.mpr (hroot c (Finset.ne_of_mem_erase hc))
  obtain ⟨Q, hQ⟩ := hdvd
  have hQ0 : Q ≠ 0 := fun h => hA0 (by rw [hQ, h, mul_zero])
  have hQdeg : Q.natDegree = 0 := by
    have h1 : A.natDegree < s := by
      rw [degree_eq_natDegree hA0] at hAdeg; exact_mod_cast hAdeg
    have h2 : A.natDegree = (s - 1) + Q.natDegree := by
      rw [hQ, natDegree_mul (show (wCo a cs).Monic by rw [← pow_one (wCo a cs), ← placeCo_const]; exact placeCo_monic a _ cs).ne_zero hQ0, natDegree_wCo]
    omega
  set lam := Q.coeff 0
  have hAl : A = C lam * wCo a cs := by rw [hQ, eq_C_of_natDegree_eq_zero hQdeg, mul_comm]
  have hlam : lam ≠ 0 := fun h => hA0 (by rw [hAl, h, map_zero, zero_mul])
  refine ⟨hk, lam, hlam, ?_, fun c hc => ?_⟩
  · have := hid cs
    rwa [hpcs, taylor_one, map_one, Polynomial.coe_one, mul_one, hAl, taylor_mul, taylor_C, Polynomial.coe_mul,
      Polynomial.coe_C] at this
  · have h1 := hidc c hc
    rw [hAl, wCo_eq a hc, taylor_mul, taylor_C, taylor_mul, taylor_X_sub_C, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X] at h1
    have htw : tw a c = ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) *
        ((taylor (a c) (wCoCo a cs c) : F[X]) : PowerSeries F) := by
      rw [wCo_eq a (Ne.symm hc), wCoCo_comm, taylor_mul, Polynomial.coe_mul]
    rw [htw] at h1
    have hne : PowerSeries.X * ((taylor (a c) (wCoCo a cs c) : F[X]) : PowerSeries F) ≠ 0 := by
      refine mul_ne_zero PowerSeries.X_ne_zero fun h0 => ?_
      have := congrArg PowerSeries.constantCoeff h0
      rw [constantCoeff_taylor, map_zero, wCoCo_comm] at this
      exact wCoCo_eval_ne a ha c cs this
    have h2 : φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) * PowerSeries.C (-k c * θ⁻¹) =
        PowerSeries.C lam := by
      refine mul_right_cancel₀ hne ?_
      rw [← h1, map_mul]; ring
    have hkθ : -k c * θ⁻¹ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (hk c hc)) (inv_ne_zero hθ)
    calc φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F)
        = φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) * PowerSeries.C (-k c * θ⁻¹) *
          PowerSeries.C (-k c * θ⁻¹)⁻¹ := by
          rw [mul_assoc _ (PowerSeries.C _), ← map_mul, mul_inv_cancel₀ hkθ, map_one, mul_one]
      _ = PowerSeries.C (-(lam * θ) / k c) := by
          rw [h2, ← map_mul]; congr 1; field_simp [hk c hc, hθ]

/-- `prop:onerel`(iii): the local multipliers found in `onerel_stag` are those of the staggered residue sequence: the
scramble is `𝓡^⋆` with `μ⋆ = λθ` and weights `k` (`ssL = resStarL`, `def:residuestar`). -/
theorem onerel_stag_gen (a : Fin s → F) (ha : Function.Injective a) (θ : F) (φ : Fin s → PowerSeries F)
    (cs : Fin s) (k : Fin s → F) (lam : F) (hcs : φ cs = PowerSeries.C lam * tw a cs)
    (hc : ∀ c, c ≠ cs → φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) =
      PowerSeries.C (-(lam * θ) / k c)) :
    ssL a θ φ = resStarL a θ cs (lam * θ) k := by
  funext c n i
  have hu : tw a c * (tw a c)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_taylor]; exact wCo_eval_ne a ha c)
  by_cases h : c = cs
  · subst h
    rw [ssL, resStarL, stagMu, if_pos rfl, stagLev, if_pos rfl, placeCo_stagK_self, taylor_pow,
      Polynomial.coe_pow, ps_inv_pow, hcs]
    have e : PowerSeries.C lam * tw a c * ((tw a c)⁻¹) ^ (n + 1) =
        PowerSeries.C lam * ((tw a c)⁻¹) ^ n := by
      rw [pow_succ]
      linear_combination (PowerSeries.C lam * ((tw a c)⁻¹) ^ n) * hu
    rw [e, PowerSeries.coeff_C_mul]; ring
  · have ht : ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) *
        (((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F))⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ (by
        rw [constantCoeff_taylor, eval_sub, eval_X, eval_C, sub_ne_zero]; exact fun h' => h (ha h'))
    have hφc : φ c = PowerSeries.C (-(lam * θ) / k c) *
        (((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F))⁻¹ := by
      rw [← hc c h, mul_assoc, ht, mul_one]
    rw [ssL, resStarL, stagMu, if_neg h, stagLev, if_neg h, placeCo_stagK_ne a cs c h, taylor_mul, taylor_pow,
      Polynomial.coe_mul, Polynomial.coe_pow, PowerSeries.mul_inv_rev, ps_inv_pow, hφc, mul_assoc,
      PowerSeries.coeff_C_mul]
    ring_nf

/-- **`prop:onerel`(iii), last sentence** — for every scramble of the frame (in particular every self-similar one):
the staggered relation `y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` and a skeleton relation `∑_c v_c y_{c,T} = 0`
on `P_{s(T+1)-1}` do not both hold at all levels `T ≥ T₀` (`s ≥ 2`; via `cor:layer`(c)). -/
theorem onerel_no_both (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (T₀ : ℕ) (cs : Fin s) (k v : Fin s → F) (hv : v ≠ 0)
    (hstag : ∀ T, T₀ ≤ T → stagVec cs k T ∈ relSpace a L T (s * T))
    (hskel : ∀ T, T₀ ≤ T → skelVec T v ∈ relSpace a L T (s * (T + 1) - 1)) : False :=
  layer_c a ha L hL hs (max T₀ (2 * s - 2)) (le_max_right _ _) cs (fun _ => k) (fun _ => v)
    fun T h1 _ => ⟨hstag T (le_trans (le_max_left _ _) h1), hv, hskel T (le_trans (le_max_left _ _) h1)⟩

end SS

end GeoSeq
