/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.EBasis

@[expose] public section

/-!
# GeoSeq stage S11: the e-basis form of self-similar scrambles (`prop:LI`(a), Faure frame)

* `ebas_eq_w` (`eq:riordanres`-type change of coordinate): `ε_{c,j}(V) = [w^j] u_c(w) V(z_c(w))`, and
  scaled: `θ^j ε_{c,j}(V) = [x^j] u_c(θx) V(z_c(θx))` (`ebas_eq_x`).
* **`LI_a`** (`prop:LI`(a), e-basis characterisation, `s = 2`): coordinate `c` of a scramble is
  self-similar with scale `θ` (digits `y_{c,n}(V) = [x^n] g_c(x) V(z_c(θx))`, `g_c(0) ≠ 0`) iff
  `T_c = diag(λ_c θ^n) · Toep(φ_c)` with `λ_c ≠ 0`, `φ_c(0) = 1`.
* `LI_a_B`: the same from the inverse matrix, `B_c = diag(μ θ^{-i}) · Toep(χ)` ⟹ self-similar (used by
  `prop:LIconv`).
* `scrGen_eq_ssGen_iff`: the functional form is the generator-matrix identity `C_c = ssGen g zθ`
  (`def:selfsim`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-! ## Substitution lemmas -/

lemma subst_wD_neg (δ : F) (f : PS) : (-f).subst (wD δ) = -(f.subst (wD δ)) := by
  rw [← coe_substAlgHom (hasSubst_wD δ), map_neg]

lemma subst_wD_inv (δ : F) (f : PS) (hf : constantCoeff f ≠ 0) :
    (f⁻¹).subst (wD δ) = (f.subst (wD δ))⁻¹ := by
  have h : f.subst (wD δ) * (f⁻¹).subst (wD δ) = 1 := by
    rw [← subst_mul (hasSubst_wD δ), PowerSeries.mul_inv_cancel _ hf, subst_wD_one]
  have hc : constantCoeff (f.subst (wD δ)) ≠ 0 := by
    intro h0; have := congrArg constantCoeff h; rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  exact ((PowerSeries.eq_inv_iff_mul_eq_one hc).2 (by rw [mul_comm]; exact h))

lemma aeval_subst_wD (δ : F) (z : PS) (V : F[X]) :
    (Polynomial.aeval z V).subst (wD δ) = Polynomial.aeval (z.subst (wD δ)) V := by
  rw [← coe_substAlgHom (hasSubst_wD δ), ← Polynomial.aeval_algHom_apply]

lemma aeval_X_add_C (a : F) (V : F[X]) :
    Polynomial.aeval (X + C a : PS) V = (Polynomial.taylor a V : PS) := by
  induction V using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.coe_add]
  | monomial n b =>
    rw [Polynomial.aeval_monomial, Polynomial.taylor_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
    rfl

/-- `z_c(t(t + δ_c)) = a_c + t`: the substitution `w = wD δ_c` inverts the local root. -/
lemma zF_subst (c : Fin 2) : (zF c : PS).subst (wD (faureDel c : F)) = X + C (faurePl c : F) := by
  fin_cases c
  · simp only [zF, Fin.zero_eta, Matrix.cons_val_zero]
    rw [subst_wD_neg, tRoot_subst_wD _ (faureDel_sq 0), faureDel_zero, faurePl_zero, map_neg,
      neg_mul, neg_neg, map_one, one_mul, map_zero, add_zero]
  · simp only [zF, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [subst_add (hasSubst_wD _), subst_wD_one, tRoot_subst_wD _ (faureDel_sq 1), faureDel_one,
      faurePl_one, map_one, one_mul, add_comm]

lemma constantCoeff_zF (c : Fin 2) : constantCoeff (zF c : PS) = faurePl c := by
  fin_cases c
  · simp [zF, constantCoeff_tRoot, faurePl]
  · simp [zF, constantCoeff_tRoot, faurePl]

lemma two_pl_sub_one (c : Fin 2) : 2 * faurePl c - 1 = (faureDel c : F) := by
  fin_cases c <;> simp [faurePl, faureDel] <;> ring

lemma constantCoeff_uF_inv (c : Fin 2) :
    constantCoeff ((C 2 * zF c - 1) * (zF c - C (faurePl c) + C (faureDel c)) : PS) = 1 := by
  rw [map_mul, map_sub, map_mul, map_add, map_sub, constantCoeff_C, constantCoeff_zF, map_one,
    constantCoeff_C, constantCoeff_C, two_pl_sub_one, sub_self, zero_add, faureDel_sq]

lemma constantCoeff_uF (c : Fin 2) : constantCoeff (uF c : PS) = 1 := by
  rw [uF, PowerSeries.constantCoeff_inv, constantCoeff_uF_inv, inv_one]

lemma uF_subst (c : Fin 2) : (uF c : PS).subst (wD (faureDel c : F)) =
    (((C 2 * X + C (faureDel c : F)) * (X + C (faureDel c : F)))⁻¹ : PS) := by
  rw [uF, subst_wD_inv _ _ (by rw [constantCoeff_uF_inv]; exact one_ne_zero),
    subst_mul (hasSubst_wD _), subst_sub (hasSubst_wD _), subst_add (hasSubst_wD _),
    subst_sub (hasSubst_wD _), subst_mul (hasSubst_wD _), subst_wD_C, subst_wD_C, subst_wD_C,
    subst_wD_one, zF_subst]
  congr 1
  rw [← two_pl_sub_one c, map_sub, map_mul, map_one]
  ring

/-- **The e-basis in the coordinate `w`** (change of coordinate, `θ = 1`):
`ε_{c,j}(V) = [w^j] u_c(w) V(z_c(w))`. -/
theorem ebas_eq_w (c : Fin 2) (j : ℕ) (V : F[X]) :
    ebas c j V = coeff j (uF c * Polynomial.aeval (zF c) V) := by
  set δ := faureDel (F := F) c
  have hδ := faureDel_sq (F := F) c
  have hδ0 := faureDel_ne (F := F) c
  rw [coeff_change δ hδ, subst_mul (hasSubst_wD δ), uF_subst, aeval_subst_wD, zF_subst,
    aeval_X_add_C, ebas]
  congr 1
  have h2 : constantCoeff (C 2 * X + C δ : PS) ≠ 0 := by simp; exact hδ0
  have h1 : constantCoeff (X + C δ : PS) ≠ 0 := by simp; exact hδ0
  rw [PowerSeries.mul_inv_rev]
  have e : ((X + C δ : PS) ^ (j + 2))⁻¹ = (X + C δ)⁻¹ * ((X + C δ) ^ (j + 1))⁻¹ := by
    rw [← PowerSeries.mul_inv_rev, ← pow_succ]
  rw [e]
  symm
  calc (X + C δ : PS)⁻¹ * (C 2 * X + C δ)⁻¹ * (Polynomial.taylor (faurePl c) V : PS) *
        ((C 2 * X + C δ) * ((X + C δ) ^ (j + 1))⁻¹)
      = ((C 2 * X + C δ) * (C 2 * X + C δ)⁻¹) * ((Polynomial.taylor (faurePl c) V : PS) *
          ((X + C δ)⁻¹ * ((X + C δ) ^ (j + 1))⁻¹)) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ h2, one_mul]

lemma rescale_aeval (θ : F) (z : PS) (V : F[X]) :
    rescale θ (Polynomial.aeval z V) = Polynomial.aeval (rescale θ z) V := by
  induction V using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n b =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext m; simp [coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]

/-- **The e-basis in the coordinate `x = w/θ`**: `θ^j ε_{c,j}(V) = [x^j] u_c(θx) V(z_c(θx))`. -/
theorem ebas_eq_x (θ : F) (c : Fin 2) (j : ℕ) (V : F[X]) :
    θ ^ j * ebas c j V =
      coeff j (rescale θ (uF c) * Polynomial.aeval (rescale θ (zF c)) V) := by
  rw [ebas_eq_w, ← rescale_aeval, ← map_mul, coeff_rescale]

/-! ## `prop:LI`(a) -/

/-- The digits `[x^n] h · u_c(θx) V(z_c(θx))` in the e-basis: `∑_{k ≤ n} h_{n-k} θ^k ε_{c,k}(V)`. -/
lemma coeff_ss_ebas (θ : F) (c : Fin 2) (h : PS) (n : ℕ) (V : F[X]) :
    coeff n (h * (rescale θ (uF c) * Polynomial.aeval (rescale θ (zF c)) V)) =
      ∑ k ∈ range (n + 1), coeff (n - k) h * θ ^ k * ebas c k V := by
  rw [mul_comm h, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k i => coeff k (rescale θ (uF c) * Polynomial.aeval (rescale θ (zF c)) V) * coeff i h)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← ebas_eq_x]; ring

/-- **`prop:LI`(a)** (e-basis characterisation, Faure frame): with `T_c` the matrix of the rows in the
e-basis (`y_{c,n} = ∑_{k ≤ n} T_c[n][k] ε_{c,k}`), coordinate `c` is self-similar with scale `θ ≠ 0`
(`y_{c,n}(V) = [x^n] g(x) V(z_c(θx))` with `g(0) ≠ 0`) iff `T_c[n][k] = λ θ^n φ_{n-k}` for `k ≤ n`, with
`λ ≠ 0`, `φ(0) = 1` (`T_c = diag(λ θ^n) · Toep(φ)`). The correspondence is `λ φ(θx) = g(x)/u_c(θx)`. -/
theorem LI_a (L : Fin 2 → ℕ → ℕ → F) (T : Fin 2 → ℕ → ℕ → F)
    (hT : ∀ c n V, scrDig (faurePl c) (L c) n V = ∑ k ∈ range (n + 1), T c n k * ebas c k V)
    (θ : F) (hθ : θ ≠ 0) (c : Fin 2) :
    (∃ g : PS, constantCoeff g ≠ 0 ∧ ∀ n V,
        scrDig (faurePl c) (L c) n V = coeff n (g * Polynomial.aeval (rescale θ (zF c)) V)) ↔
      (∃ lam : F, lam ≠ 0 ∧ ∃ φ : PS, constantCoeff φ = 1 ∧
        ∀ n k, k ≤ n → T c n k = lam * θ ^ n * coeff (n - k) φ) := by
  have hu : constantCoeff (rescale θ (uF c) : PS) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_uF]
  set uθ : PS := rescale θ (uF c)
  constructor
  · rintro ⟨g, hg0, hg⟩
    set Ω : PS := g * uθ⁻¹
    have hgΩ : g = Ω * uθ := by
      rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hu]; exact one_ne_zero), mul_one]
    have hΩ0 : constantCoeff Ω ≠ 0 := by
      rw [map_mul, PowerSeries.constantCoeff_inv, hu, inv_one, mul_one]; exact hg0
    -- uniqueness of `T_c`
    have hTe : ∀ n k, k ≤ n → T c n k = coeff (n - k) Ω * θ ^ k := by
      intro n
      have hd := ebas_indep c n (fun k => T c n k - coeff (n - k) Ω * θ ^ k) (fun V => by
        have h1 := hT c n V
        rw [hg n V, hgΩ, mul_assoc, coeff_ss_ebas] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [← h1]; exact sub_self _)
      intro k hk
      exact sub_eq_zero.1 (hd k hk)
    refine ⟨constantCoeff Ω, hΩ0, C (constantCoeff Ω)⁻¹ * rescale θ⁻¹ Ω, ?_, fun n k hk => ?_⟩
    · rw [map_mul, constantCoeff_C, ← coeff_zero_eq_constantCoeff_apply (rescale θ⁻¹ Ω),
        coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply,
        inv_mul_cancel₀ hΩ0]
    · rw [hTe n k hk, coeff_C_mul, coeff_rescale, inv_pow,
        show n = (n - k) + k by omega, pow_add]
      simp only [show n - k + k - k = n - k by omega]
      field_simp
  · rintro ⟨lam, hlam, φ, hφ, hform⟩
    refine ⟨C lam * rescale θ φ * uθ, ?_, fun n V => ?_⟩
    · rw [map_mul, map_mul, constantCoeff_C, hu, mul_one, ← coeff_zero_eq_constantCoeff_apply,
        coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply, hφ, mul_one]
      exact hlam
    · rw [mul_assoc (C lam * rescale θ φ), coeff_ss_ebas, hT]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := by simp at hk; omega
      rw [hform n k hk', coeff_C_mul, coeff_rescale, show n = (n - k) + k by omega, pow_add]
      simp only [show n - k + k - k = n - k by omega]
      ring

/-- `prop:LI`(a) from the inverse matrix: if `B_c[i][j] = μ θ^{-i} χ_{i-j}` (`μ ≠ 0`, `χ(0) ≠ 0`), then
coordinate `c` is self-similar with scale `θ`, multiplier `g = u_c(θx) / (μ χ(x))`. -/
theorem LI_a_B (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (θ : F) (hθ : θ ≠ 0) (c : Fin 2) (μ : F) (hμ : μ ≠ 0) (χ : PS) (hχ : constantCoeff χ ≠ 0)
    (hform : ∀ i j, j ≤ i → B c i j = μ * (θ ^ i)⁻¹ * coeff (i - j) χ) :
    ∃ g : PS, constantCoeff g ≠ 0 ∧ ∀ n V,
      scrDig (faurePl c) (L c) n V = coeff n (g * Polynomial.aeval (rescale θ (zF c)) V) := by
  have hu : constantCoeff (rescale θ (uF c) : PS) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_uF]
  set uθ : PS := rescale θ (uF c)
  refine ⟨C μ⁻¹ * χ⁻¹ * uθ, ?_, fun n V => ?_⟩
  · rw [map_mul, map_mul, constantCoeff_C, PowerSeries.constantCoeff_inv, hu, mul_one]
    exact mul_ne_zero (inv_ne_zero hμ) (inv_ne_zero hχ)
  · have hBd : ∀ i, B c i i ≠ 0 := fun i => by
      rw [hform i i le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
      exact mul_ne_zero (mul_ne_zero hμ (inv_ne_zero (pow_ne_zero _ hθ))) hχ
    refine tri_det (B c) hBd (fun i => ebas c i V) (fun j => scrDig (faurePl c) (L c) j V)
      (fun j => coeff j (C μ⁻¹ * χ⁻¹ * uθ * Polynomial.aeval (rescale θ (zF c)) V))
      (fun i => hB c i V) (fun i => ?_) n
    -- `ε_i = ∑_j μ θ^{-i} χ_{i-j} [x^j](g V(zθ))`
    have hx := ebas_eq_x θ c i V
    have hsum : ∑ j ∈ range (i + 1), B c i j *
        coeff j (C μ⁻¹ * χ⁻¹ * uθ * Polynomial.aeval (rescale θ (zF c)) V) =
        μ * (θ ^ i)⁻¹ * coeff i (χ * (C μ⁻¹ * χ⁻¹ * uθ * Polynomial.aeval (rescale θ (zF c)) V)) := by
      rw [mul_comm χ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun j k => coeff j (C μ⁻¹ * χ⁻¹ * uθ * Polynomial.aeval (rescale θ (zF c)) V) * coeff k χ),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < i + 1 := by simpa using hj
      rw [hform i j (by omega)]
      ring
    rw [hsum]
    have : χ * (C μ⁻¹ * χ⁻¹ * uθ * Polynomial.aeval (rescale θ (zF c)) V) =
        C μ⁻¹ * (uθ * Polynomial.aeval (rescale θ (zF c)) V) := by
      calc χ * (C μ⁻¹ * χ⁻¹ * uθ * Polynomial.aeval (rescale θ (zF c)) V)
          = (χ * χ⁻¹) * (C μ⁻¹ * (uθ * Polynomial.aeval (rescale θ (zF c)) V)) := by ring
        _ = _ := by rw [PowerSeries.mul_inv_cancel _ hχ, one_mul]
    rw [this, coeff_C_mul, ← hx]
    field_simp

/-- **Self-similar scrambles as generator matrices** (`def:selfsim`): the scrambled Faure frame equals
`ssGen g zθ` iff the digit functionals of every coordinate are `V ↦ [x^n] g_c V(zθ_c)`. -/
theorem scrGen_eq_ssGen_iff (L : Fin 2 → ℕ → ℕ → F) (g zθ : Fin 2 → PS) :
    scrGen faurePl L = ssGen g zθ ↔
      ∀ c n V, scrDig (faurePl c) (L c) n V = coeff n (g c * Polynomial.aeval (zθ c) V) := by
  have hmono : ∀ c n k, scrGen faurePl L c n k = scrDig (faurePl c) (L c) n (Polynomial.X ^ k) := by
    intro c n k
    rw [scrGen, scrDig]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.taylor_X_pow, Polynomial.coeff_X_add_C_pow, pas]; ring
  constructor
  · intro h c n V
    have hV := poly_sum_range V (V.natDegree + 1) (Nat.lt_succ_self _)
    have e1 : scrDig (faurePl c) (L c) n V = ∑ m ∈ range (V.natDegree + 1),
        V.coeff m * scrDig (faurePl c) (L c) n (Polynomial.X ^ m) := by
      conv_lhs => rw [hV]
      simp only [scrDig, map_sum, Polynomial.finsetSum_coeff, Polynomial.taylor_mul,
        Polynomial.taylor_C, Polynomial.coeff_C_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
    have e2 : coeff n (g c * Polynomial.aeval (zθ c) V) = ∑ m ∈ range (V.natDegree + 1),
        V.coeff m * coeff n (g c * zθ c ^ m) := by
      rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [mul_smul_comm, map_smul, smul_eq_mul]
    rw [e1, e2]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hmono, h]; rfl
  · intro h
    funext c n k
    rw [hmono, h, ssGen, Polynomial.aeval_X_pow]

end GeoSeq
