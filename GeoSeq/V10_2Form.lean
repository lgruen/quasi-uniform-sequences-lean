/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_2Res
public import GeoSeq.V10_2Defs
public import GeoSeq.V98SS
public import GeoSeq.SSFrame

@[expose] public section

/-!
# GeoSeq stage V10-2 (part 2): self-similar scrambles in residue form (`lem:resform`(b))

* `aeval_taylor`, `taylor_subst`: `(taylor_a V)(Z) = V(a + Z)`.
* Local roots: `locU_subst` (`u(zθ_c - a_c) = x`), `locRoots_exists`, `locRoots_unique` (the paper's "unique power
  series `z_c(x)` with `w(z_c(x)) = x`", scaled by `θ`).
* **`ssMul_digit`** (`lem:resform`(b), `⇐`, the change of variable `lem:reschange` with `u = w/θ`): the self-similar
  scramble with multipliers `g_c = θ φ_c(z_c(θx)) z_c'(θx)` has digits `Res_{a_c}(V φ_c (θ/w)^{n+1} dz)`.
* `ssMul_locMul`, `locMul_ssMul`: the two maps `g ↦ φ`, `φ ↦ g` are mutually inverse; `constantCoeff_locMul`,
  `constantCoeff_ssMul`: units go to units.
* **`selfsim_eq_ssL`** (`⇒`): a self-similar scramble (`def:selfsim` as written) has generator matrices
  `scrGen a (ssL a θ φ)` with `φ = locMul a θ g`; **`ssL_selfsim`** (`⇐`); **`resform_b`** (the iff).
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F] {s : ℕ}

local notation "PX" => (PowerSeries.X : PowerSeries F)

lemma algebraMap_ps (r : F) : algebraMap F (PowerSeries F) r = PowerSeries.C r := rfl

/-- `taylor_a p` evaluated at `Z` is `p(Z + a)`. -/
lemma aeval_taylor (a : F) (Z : PowerSeries F) (p : F[X]) :
    Polynomial.aeval Z (taylor a p) = Polynomial.aeval (Z + PowerSeries.C a) p := by
  rw [taylor_apply, Polynomial.aeval_comp]
  simp

/-- `(taylor_a V)(z - a) = V(z)` as a substitution of power series. -/
lemma taylor_subst (a : F) (z : PowerSeries F) (hz : PowerSeries.constantCoeff z = a) (V : F[X]) :
    ((taylor a V : F[X]) : PowerSeries F).subst (z - PowerSeries.C a) = Polynomial.aeval z V := by
  have hs : PowerSeries.HasSubst (z - PowerSeries.C a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hz])
  rw [PowerSeries.subst_coe hs, aeval_taylor, sub_add_cancel]

lemma hasSubst_shift (z : PowerSeries F) (a : F) (hz : PowerSeries.constantCoeff z = a) :
    PowerSeries.HasSubst (z - PowerSeries.C a) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hz])

lemma subst_one' (Z : PowerSeries F) (hZ : PowerSeries.HasSubst Z) : (1 : PowerSeries F).subst Z = 1 := by
  rw [← PowerSeries.coe_substAlgHom hZ, map_one]

lemma subst_C' (Z : PowerSeries F) (hZ : PowerSeries.HasSubst Z) (r : F) :
    (PowerSeries.C r).subst Z = PowerSeries.C r := by
  rw [← PowerSeries.coe_substAlgHom hZ, ← algebraMap_ps, AlgHom.commutes, algebraMap_ps]

/-- Substitution commutes with the inverse of a unit. -/
lemma subst_inv' (Z : PowerSeries F) (hZ : PowerSeries.HasSubst Z) (f : PowerSeries F)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hf' : PowerSeries.constantCoeff (f.subst Z) ≠ 0) :
    (f⁻¹).subst Z = (f.subst Z)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one hf', ← PowerSeries.subst_mul hZ, PowerSeries.inv_mul_cancel _ hf,
    subst_one' Z hZ]

section LocRoot
variable (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F)

/-- `(zθ_c - a_c) · w_c(zθ_c) = θ x`. -/
lemma locRoot_shift (hz : IsLocRoots a θ zθ) (c : Fin s) :
    (zθ c - PowerSeries.C (a c)) * Polynomial.aeval (zθ c) (wCo a c) = PowerSeries.C θ * PX := by
  rw [← (hz c).2, wPoly_eq a c, map_mul]
  simp

/-- `u(zθ_c - a_c) = x`: the scaled local root inverts `u = w/θ` at `a_c`. -/
lemma locU_subst (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (c : Fin s) :
    ((locU a θ c : F[X]) : PowerSeries F).subst (zθ c - PowerSeries.C (a c)) = PX := by
  rw [PowerSeries.subst_coe (hasSubst_shift _ _ (hz c).1), locU, map_mul, aeval_taylor, sub_add_cancel,
    (hz c).2, Polynomial.aeval_C, algebraMap_ps, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hθ, map_one, one_mul]

lemma constantCoeff_locU (c : Fin s) : PowerSeries.constantCoeff ((locU a θ c : F[X]) : PowerSeries F) = 0 := by
  rw [locU, Polynomial.coe_mul, map_mul, constantCoeff_taylor]
  simp only [wPoly, Polynomial.eval_prod, eval_sub, eval_X, eval_C]
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ c) (sub_self _))

end LocRoot

section Digit
variable (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F)

/-- A power series with zero constant term is `x` times its shift. -/
lemma eq_X_mul_shift (Z : PowerSeries F) (hZ : PowerSeries.constantCoeff Z = 0) :
    Z = PX * PowerSeries.mk fun i => PowerSeries.coeff (i + 1) Z := by
  ext i
  rcases i with _ | i
  · simp [hZ]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

/-- **`lem:resform`(b), `⇐`**: for the scaled local roots `zθ` and any local multipliers `φ_c` (series in
`t = z - a_c`), the self-similar scramble with multipliers `g_c = ssMul a zθ φ c = θ φ_c(z_c(θx)) z_c'(θx)` has
digits `[x^n] g_c V(z_c(θx)) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz)` (`frDigit a (ssL a θ φ)`, `ssL_digit`). The proof is
the change of variable `lem:reschange` (`reschange`, every characteristic) with `x = u(t) = w(a_c + t)/θ` read
backwards: `t = zθ_c(x) - a_c = x κ(x)`. -/
theorem ssMul_digit (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ)
    (φ : Fin s → PowerSeries F) (c : Fin s) (n : ℕ) (V : F[X]) :
    PowerSeries.coeff n (ssMul a zθ φ c * Polynomial.aeval (zθ c) V) = frDigit a (ssL a θ φ) c n V := by
  rw [ssL_digit]
  set Z := zθ c - PowerSeries.C (a c) with hZdef
  have hZ0 : PowerSeries.constantCoeff Z = 0 := by simp [Z, (hz c).1]
  have hZs : PowerSeries.HasSubst Z := PowerSeries.HasSubst.of_constantCoeff_zero' hZ0
  set κ : PowerSeries F := PowerSeries.mk fun i => PowerSeries.coeff (i + 1) Z with hκdef
  have hκ : Z = PX * κ := eq_X_mul_shift Z hZ0
  set E := Polynomial.aeval (zθ c) (wCo a c) with hEdef
  have hκE : κ * E = PowerSeries.C θ := by
    have h1 : PX * (κ * E) = PX * PowerSeries.C θ := by
      rw [← mul_assoc, ← hκ, locRoot_shift a θ zθ hz c, mul_comm]
    exact mul_left_cancel₀ PowerSeries.X_ne_zero h1
  have hcc : PowerSeries.constantCoeff κ * PowerSeries.constantCoeff E = θ := by
    rw [← map_mul, hκE, PowerSeries.constantCoeff_C]
  have hκ0 : PowerSeries.constantCoeff κ ≠ 0 := left_ne_zero_of_mul (hcc ▸ hθ)
  have hE0 : PowerSeries.constantCoeff E ≠ 0 := right_ne_zero_of_mul (hcc ▸ hθ)
  set tw : PowerSeries F := ((taylor (a c) (wCo a c) : F[X]) : PowerSeries F) with htwdef
  have htw0 : PowerSeries.constantCoeff tw ≠ 0 := by
    rw [htwdef, constantCoeff_taylor]; exact wCo_eval_ne a ha c
  have htw : tw.subst Z = E := taylor_subst (a c) (zθ c) (hz c).1 (wCo a c)
  have htwinv : (tw⁻¹).subst Z = E⁻¹ := by
    rw [subst_inv' Z hZs tw htw0 (by rw [htw]; exact hE0), htw]
  set tV : PowerSeries F := ((taylor (a c) V : F[X]) : PowerSeries F) with htVdef
  have htV : tV.subst Z = Polynomial.aeval (zθ c) V := taylor_subst (a c) (zθ c) (hz c).1 V
  have key := reschange κ κ⁻¹ (PowerSeries.mul_inv_cancel κ hκ0)
    (tV * (φ c * (PowerSeries.C θ * tw⁻¹) ^ (n + 1))) n
  rw [← hκ, PowerSeries.subst_mul hZs, PowerSeries.subst_mul hZs, PowerSeries.subst_pow hZs,
    PowerSeries.subst_mul hZs, subst_C' Z hZs, htwinv, htV] at key
  have hdZ : PowerSeries.derivative Z = PowerSeries.derivative (zθ c) := by
    simp [Z]
  have hθE : PowerSeries.C θ * E⁻¹ = κ := by
    rw [← hκE, mul_assoc, PowerSeries.mul_inv_cancel _ hE0, mul_one]
  rw [hdZ, hθE] at key
  have hL : PowerSeries.coeff n (tV * (φ c * (PowerSeries.C θ * tw⁻¹) ^ (n + 1))) =
      θ ^ (n + 1) * PowerSeries.coeff n (tV * (φ c * (tw⁻¹) ^ (n + 1))) := by
    rw [mul_pow, ← map_pow, show tV * (φ c * (PowerSeries.C (θ ^ (n + 1)) * tw⁻¹ ^ (n + 1))) =
      PowerSeries.C (θ ^ (n + 1)) * (tV * (φ c * tw⁻¹ ^ (n + 1))) by ring, PowerSeries.coeff_C_mul]
  have hκκ : κ ^ (n + 1) * κ⁻¹ ^ (n + 1) = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel κ hκ0, one_pow]
  have hR : Polynomial.aeval (zθ c) V * ((φ c).subst Z * κ ^ (n + 1)) * PowerSeries.derivative (zθ c) *
      κ⁻¹ ^ (n + 1) = ssMul a zθ φ c * Polynomial.aeval (zθ c) V := by
    rw [ssMul, ← hZdef]
    linear_combination (Polynomial.aeval (zθ c) V * (φ c).subst Z * PowerSeries.derivative (zθ c)) * hκκ
  rw [← hR, ← key, hL]

end Digit

section Inverse
variable (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F)

lemma constantCoeff_subst0 (Z : PowerSeries F) (hZ : PowerSeries.constantCoeff Z = 0) (f : PowerSeries F) :
    PowerSeries.constantCoeff (f.subst Z) = PowerSeries.constantCoeff f := by
  have h := PowerSeries.constantCoeff_subst_of_constantCoeff_zero hZ f
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

lemma aeval_locU (c : Fin s) (Q : PowerSeries F) :
    Polynomial.aeval Q (locU a θ c) = PowerSeries.C θ⁻¹ * Polynomial.aeval (Q + PowerSeries.C (a c)) (wPoly a) := by
  rw [locU, map_mul, aeval_taylor, Polynomial.aeval_C, algebraMap_ps]

lemma hasSubst_locU (c : Fin s) : PowerSeries.HasSubst ((locU a θ c : F[X]) : PowerSeries F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_locU a θ c)

/-- `[t] u = θ^{-1} w_c(a_c)` (`w = (z - a_c) w_c`). -/
lemma coeff_one_locU (c : Fin s) : (locU a θ c).coeff 1 = θ⁻¹ * (wCo a c).eval (a c) := by
  rw [locU, coeff_C_mul, wPoly_eq a c, taylor_mul]
  simp only [map_sub, taylor_X, taylor_C, add_sub_cancel_right, coeff_X_mul, taylor_coeff_zero]

/-- `[x] zθ_c ≠ 0` for the scaled local roots. -/
lemma coeff_one_locRoot (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (c : Fin s) :
    PowerSeries.coeff 1 (zθ c) * (θ⁻¹ * (wCo a c).eval (a c)) = 1 := by
  have h := congrArg (PowerSeries.coeff 1) (locU_subst a θ zθ hθ hz c)
  have hZ0 : PowerSeries.constantCoeff (zθ c - PowerSeries.C (a c)) = 0 := by simp [(hz c).1]
  have hd := congrArg PowerSeries.constantCoeff (PowerSeries.derivative_subst (f := ((locU a θ c : F[X]) :
    PowerSeries F)) (hasSubst_shift _ _ (hz c).1))
  rw [locU_subst a θ zθ hθ hz c, PowerSeries.derivative_X, map_one, map_mul,
    constantCoeff_subst0 _ hZ0] at hd
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add,
    Nat.cast_zero, mul_one, Polynomial.coeff_coe, map_sub, PowerSeries.coeff_C, coeff_one_locU] at hd
  simp only [one_ne_zero, ite_false, sub_zero] at hd
  rw [hd]; ring

/-- `φ ↦ g ↦ φ`: `ssMul ∘ locMul = id` on multipliers (`lem:resform`(b), the two maps are mutually inverse). -/
theorem ssMul_locMul (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) :
    ssMul a zθ (locMul a θ g) = g := by
  funext c
  have hZs := hasSubst_shift (zθ c) (a c) (hz c).1
  have hU := hasSubst_locU a θ c
  have hd := PowerSeries.derivative_subst (f := ((locU a θ c : F[X]) : PowerSeries F)) hZs
  rw [locU_subst a θ zθ hθ hz c, PowerSeries.derivative_X, PowerSeries.derivative_coe] at hd
  have hdZ : PowerSeries.derivative (zθ c - PowerSeries.C (a c)) = PowerSeries.derivative (zθ c) := by simp
  rw [hdZ] at hd
  rw [ssMul, locMul, PowerSeries.subst_mul hZs, PowerSeries.subst_comp_subst_apply hU hZs,
    locU_subst a θ zθ hθ hz c, PowerSeries.X_subst, mul_assoc, ← hd, mul_one]

/-- `g ↦ φ ↦ g`: `locMul ∘ ssMul = id` (`lem:resform`(b)); uses that `zθ_c - a_c` is also a LEFT inverse of `u`. -/
theorem locMul_ssMul (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ)
    (φ : Fin s → PowerSeries F) : locMul a θ (ssMul a zθ φ) = φ := by
  funext c
  have hZs := hasSubst_shift (zθ c) (a c) (hz c).1
  have hU := hasSubst_locU a θ c
  have hunit : IsUnit (PowerSeries.coeff 1 ((locU a θ c : F[X]) : PowerSeries F)) := by
    rw [Polynomial.coeff_coe, coeff_one_locU]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hθ) (wCo_eval_ne a ha c))
  have hleft : (zθ c - PowerSeries.C (a c)).subst ((locU a θ c : F[X]) : PowerSeries F) = PX :=
    PowerSeries.subst_eq_X_of_subst_eq_X _ (constantCoeff_locU a θ c) hunit hZs (locU_subst a θ zθ hθ hz c)
  have hd := PowerSeries.derivative_subst (f := zθ c - PowerSeries.C (a c)) hU
  rw [hleft, PowerSeries.derivative_X, PowerSeries.derivative_coe] at hd
  have hdZ : PowerSeries.derivative (zθ c - PowerSeries.C (a c)) = PowerSeries.derivative (zθ c) := by simp
  rw [hdZ] at hd
  rw [locMul, ssMul, PowerSeries.subst_mul hU, PowerSeries.subst_comp_subst_apply hZs hU, hleft,
    PowerSeries.X_subst, mul_assoc, ← hd, mul_one]

/-- The local multipliers of unit multipliers are units: `φ_c(a_c) = g_c(0) θ^{-1} w_c(a_c)`. -/
theorem constantCoeff_locMul (g : Fin s → PowerSeries F) (c : Fin s) :
    PowerSeries.constantCoeff (locMul a θ g c) =
      PowerSeries.constantCoeff (g c) * (θ⁻¹ * (wCo a c).eval (a c)) := by
  rw [locMul, map_mul, constantCoeff_subst0 _ (constantCoeff_locU a θ c),
    show PowerSeries.constantCoeff ((derivative (locU a θ c) : F[X]) : PowerSeries F) =
      (derivative (locU a θ c)).coeff 0 by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe],
    coeff_derivative, coeff_one_locU]
  simp

/-- The multipliers of unit local multipliers are units: `g_c(0) = φ_c(a_c) · [x] zθ_c`. -/
theorem constantCoeff_ssMul (φ : Fin s → PowerSeries F) (hz : IsLocRoots a θ zθ) (c : Fin s) :
    PowerSeries.constantCoeff (ssMul a zθ φ c) =
      PowerSeries.constantCoeff (φ c) * PowerSeries.coeff 1 (zθ c) := by
  have hZ0 : PowerSeries.constantCoeff (zθ c - PowerSeries.C (a c)) = 0 := by simp [(hz c).1]
  rw [ssMul, map_mul, constantCoeff_subst0 _ hZ0,
    show PowerSeries.constantCoeff (PowerSeries.derivative (zθ c)) = PowerSeries.coeff 1 (zθ c) by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]; simp]

/-- **Existence of the scaled local roots** (`def:selfsim`; the paper's `z_c(x)`, `w(z_c(x)) = x`, at `θx`). -/
theorem locRoots_exists (ha : Function.Injective a) (hθ : θ ≠ 0) : ∃ zθ, IsLocRoots a θ zθ := by
  have hunit : ∀ c, IsUnit (PowerSeries.coeff 1 ((locU a θ c : F[X]) : PowerSeries F)) := fun c => by
    rw [Polynomial.coeff_coe, coeff_one_locU]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hθ) (wCo_eval_ne a ha c))
  refine ⟨fun c => PowerSeries.C (a c) +
    PowerSeries.substInvOfIsUnit ((locU a θ c : F[X]) : PowerSeries F) (hunit c), fun c => ⟨?_, ?_⟩⟩
  · simp
  · set Q := PowerSeries.substInvOfIsUnit ((locU a θ c : F[X]) : PowerSeries F) (hunit c)
    have hQ : ((locU a θ c : F[X]) : PowerSeries F).subst Q = PX :=
      PowerSeries.subst_substInvOfIsUnit_right _ (constantCoeff_locU a θ c) (hunit c)
    rw [PowerSeries.subst_coe (PowerSeries.HasSubst.substInvOfIsUnit _ (hunit c)), aeval_locU] at hQ
    show Polynomial.aeval (PowerSeries.C (a c) + Q) (wPoly a) = _
    rw [add_comm, ← hQ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_mul]

/-- **Uniqueness of the scaled local roots.** -/
theorem locRoots_unique (ha : Function.Injective a) (hθ : θ ≠ 0) (z₁ z₂ : Fin s → PowerSeries F)
    (h₁ : IsLocRoots a θ z₁) (h₂ : IsLocRoots a θ z₂) : z₁ = z₂ := by
  funext c
  have hunit : IsUnit (PowerSeries.coeff 1 ((locU a θ c : F[X]) : PowerSeries F)) := by
    rw [Polynomial.coeff_coe, coeff_one_locU]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hθ) (wCo_eval_ne a ha c))
  have e₁ := PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X _ (constantCoeff_locU a θ c) hunit
    (hasSubst_shift _ _ (h₁ c).1) (locU_subst a θ z₁ hθ h₁ c)
  have e₂ := PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X _ (constantCoeff_locU a θ c) hunit
    (hasSubst_shift _ _ (h₂ c).1) (locU_subst a θ z₂ hθ h₂ c)
  exact sub_left_injective (e₁.trans e₂.symm)

end Inverse

section Gen
variable (a : Fin s → F) (θ : F)

/-- Entry `C_c[n][k]` of `scrGen a L` is digit `n` of coordinate `c` at the index polynomial `z^k`. -/
lemma scrGen_eq_frDigit (L : Fin s → ℕ → ℕ → F) (c : Fin s) (n k : ℕ) :
    scrGen a L c n k = frDigit a L c n (X ^ k) := by
  rw [scrGen, frDigit]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_taylor_X_pow]

/-- The digits `frDigit a L` are determined by the generator matrices `scrGen a L`. -/
lemma frDigit_eq_sum (L : Fin s → ℕ → ℕ → F) (c : Fin s) (n : ℕ) (V : F[X]) :
    frDigit a L c n V = ∑ j ∈ range (V.natDegree + 1), scrGen a L c n j * V.coeff j := by
  rw [← frDigit_vecPoly]
  congr 1
  rw [vecPoly, ← as_sum_range_C_mul_X_pow]

lemma frDigit_congr {L₁ L₂ : Fin s → ℕ → ℕ → F} (h : scrGen a L₁ = scrGen a L₂) :
    frDigit a L₁ = frDigit a L₂ := by
  funext c n V; rw [frDigit_eq_sum, frDigit_eq_sum, h]

/-- **`lem:resform`(b), `⇐`, generator matrices**: the residue form `scrGen a (ssL a θ φ)` is the self-similar
scramble with the multipliers `g = ssMul a zθ φ` (`def:selfsim`: `C_c[n][k] = [x^n] g_c z_c(θx)^k`). -/
theorem ssL_eq_ssGen (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (φ : Fin s → PowerSeries F) :
    scrGen a (ssL a θ φ) = ssGen (ssMul a zθ φ) zθ := by
  funext c n k
  rw [scrGen_eq_frDigit, ← ssMul_digit a θ zθ ha hθ hz, ssGen, Polynomial.aeval_X_pow]

/-- **`lem:resform`(b), `⇒`, generator matrices**: the self-similar scramble with multipliers `g` is the residue
form with the local multipliers `φ = locMul a θ g`. -/
theorem ssGen_eq_ssL (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) :
    ssGen g zθ = scrGen a (ssL a θ (locMul a θ g)) := by
  rw [ssL_eq_ssGen a θ ha hθ zθ hz, ssMul_locMul a θ zθ hθ hz]

/-- **`def:selfsim` ⇒ residue form, digit by digit**: a self-similar scramble (as written) has the digits
`y_{c,n}(V) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz)` of `ssL a θ φ`, `φ = locMul a θ g`. -/
theorem selfsim_frDigit (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) : frDigit a L = frDigit a (ssL a θ (locMul a θ g)) := by
  obtain ⟨_, zθ, hz, hgen⟩ := hL
  exact frDigit_congr a (hgen.trans (ssGen_eq_ssL a θ ha hθ zθ hz g))

/-- `def:selfsim` ⇒ the generator matrices of the residue form with `φ = locMul a θ g`. -/
theorem selfsim_scrGen (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) : scrGen a L = scrGen a (ssL a θ (locMul a θ g)) := by
  obtain ⟨_, zθ, hz, hgen⟩ := hL
  exact hgen.trans (ssGen_eq_ssL a θ ha hθ zθ hz g)

/-- The local multipliers of a self-similar scramble are units. -/
theorem selfsim_locMul_unit (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (c : Fin s) :
    PowerSeries.constantCoeff (locMul a θ g c) ≠ 0 := by
  rw [constantCoeff_locMul]
  exact mul_ne_zero (hL.1 c) (mul_ne_zero (inv_ne_zero hθ) (wCo_eval_ne a ha c))

/-- **`lem:resform`(b)** (as stated): a scramble of the frame is self-similar with scale `θ` (`def:selfsim`, for
some unit multipliers `g_c`) if and only if there are unit local multipliers `φ_c` (series in `t = z - a_c`) with
`y_{c,n}(V) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz) = θ^{n+1} [t^n] V(a_c + t) φ_c(t) w_c(a_c + t)^{-n-1}` for all `c, n, V`.
The correspondence is `φ = locMul a θ g`, `g = ssMul a zθ φ` (`selfsim_frDigit`, `ssL_selfsim`, mutually inverse by
`ssMul_locMul`, `locMul_ssMul`). -/
theorem resform_b (ha : Function.Injective a) (hθ : θ ≠ 0) (L : Fin s → ℕ → ℕ → F) :
    (∃ g, IsSelfSim a θ g L) ↔ ∃ φ : Fin s → PowerSeries F, (∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) ∧
      ∀ c n V, frDigit a L c n V = θ ^ (n + 1) * PowerSeries.coeff n (((taylor (a c) V : F[X]) : PowerSeries F) *
        (φ c * (((taylor (a c) (wCo a c) : F[X]) : PowerSeries F)⁻¹) ^ (n + 1))) := by
  constructor
  · rintro ⟨g, hL⟩
    refine ⟨locMul a θ g, selfsim_locMul_unit a θ ha hθ g L hL, fun c n V => ?_⟩
    rw [selfsim_frDigit a θ ha hθ g L hL, ssL_digit]
  · rintro ⟨φ, hφ, hdig⟩
    obtain ⟨zθ, hz⟩ := locRoots_exists a θ ha hθ
    refine ⟨ssMul a zθ φ, fun c => ?_, zθ, hz, ?_⟩
    · rw [constantCoeff_ssMul a θ zθ φ hz]
      refine mul_ne_zero (hφ c) fun h0 => ?_
      have := coeff_one_locRoot a θ zθ hθ hz c
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    · rw [← ssL_eq_ssGen a θ ha hθ zθ hz φ]
      funext c n k
      rw [scrGen_eq_frDigit, scrGen_eq_frDigit, hdig, ssL_digit]

/-- The scramble `ssL a θ φ` with unit local multipliers is self-similar (`def:selfsim` as written) with the
multipliers `ssMul a zθ φ`. -/
theorem ssL_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) :
    IsSelfSim a θ (ssMul a zθ φ) (ssL a θ φ) := by
  refine ⟨fun c => ?_, zθ, hz, ssL_eq_ssGen a θ ha hθ zθ hz φ⟩
  rw [constantCoeff_ssMul a θ zθ φ hz]
  refine mul_ne_zero (hφ c) fun h0 => ?_
  have := coeff_one_locRoot a θ zθ hθ hz c
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- **`lem:residue-t0`, self-similarity clause (`def:selfsim` as written)**: the residue sequence `𝓡_v` is the
self-similar scramble with scale `θ` and the explicit multipliers `g_c = v_c^{-1} · d/dx z_c(θx)`
(`= θ v_c^{-1} z_c'(θx)`; local multipliers `φ_c = 1/v_c`). -/
theorem resSeq_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (v : Fin s → F) (hv : ∀ c, v c ≠ 0) :
    IsSelfSim a θ (fun c => PowerSeries.C (v c)⁻¹ * PowerSeries.derivative (zθ c)) (resL a θ v) := by
  have hφ := ssL_selfsim a θ ha hθ zθ hz (fun c => PowerSeries.C (v c)⁻¹)
    (fun c => by rw [PowerSeries.constantCoeff_C]; exact inv_ne_zero (hv c))
  have hres : ssL a θ (fun c => PowerSeries.C (v c)⁻¹) = resL a θ v := by
    rw [ssL_const a θ _ (fun c => (v c)⁻¹) (fun c => rfl)]; simp only [inv_inv]
  have hg : ssMul a zθ (fun c => PowerSeries.C (v c)⁻¹) =
      fun c => PowerSeries.C (v c)⁻¹ * PowerSeries.derivative (zθ c) := by
    funext c; rw [ssMul, subst_C' _ (hasSubst_shift _ _ (hz c).1)]
  rw [← hres, ← hg]; exact hφ

/-- **The staggered residue sequence is self-similar (`def:selfsim` as written)**: `𝓡^⋆` (`resStarL`, staggered place
`c⋆`, `μ⋆ ≠ 0`, weights `k_c ≠ 0`) is the residue form with local multipliers `φ_{c⋆} = μ⋆ w_{c⋆}/θ`,
`φ_c = μ_c/(z - a_{c⋆})`, `μ_c = -μ⋆/k_c` (`def:residuestar`), hence self-similar with multipliers `ssMul a zθ φ`. -/
theorem resStar_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (cs : Fin s) (μs : F) (hμ : μs ≠ 0) (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) :
    ∃ φ : Fin s → PowerSeries F, IsSelfSim a θ (ssMul a zθ φ) (resStarL a θ cs μs k) := by
  set φ : Fin s → PowerSeries F := fun c => if c = cs then
    PowerSeries.C (μs / θ) * ((taylor (a cs) (wCo a cs) : F[X]) : PowerSeries F) else
    PowerSeries.C (-μs / k c) * (((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F))⁻¹ with hφdef
  have hlin : ∀ c, c ≠ cs → PowerSeries.constantCoeff
      (((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F)) ≠ 0 := fun c hc => by
    rw [constantCoeff_taylor, eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr (fun h => hc (ha h))
  have hcs : φ cs = PowerSeries.C (μs / θ) * ((taylor (a cs) (wCo a cs) : F[X]) : PowerSeries F) := by
    simp [hφdef]
  have hc : ∀ c, c ≠ cs → φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) =
      PowerSeries.C (-(μs / θ * θ) / k c) := fun c hc => by
    simp only [hφdef, hc, ↓reduceIte]
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ (hlin c hc), mul_one, div_mul_cancel₀ μs hθ]
  have hgen := onerel_stag_gen a ha θ φ cs k (μs / θ) hcs hc
  rw [div_mul_cancel₀ μs hθ] at hgen
  have hunit : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0 := fun c => by
    by_cases h : c = cs
    · subst h; rw [hcs, map_mul, PowerSeries.constantCoeff_C, constantCoeff_taylor]
      exact mul_ne_zero (div_ne_zero hμ hθ) (wCo_eval_ne a ha c)
    · simp only [hφdef, h, ↓reduceIte, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv]
      exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hμ) (hk c h)) (inv_ne_zero (hlin c h))
  exact ⟨φ, hgen ▸ ssL_selfsim a θ ha hθ zθ hz φ hunit⟩

end Gen

end GeoSeq
