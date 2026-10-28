/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Law

@[expose] public section

/-!
# GeoSeq stage S3: the law of the Faure frame in the multipliers (`lem:gform`)

Dimension `s = 2`, Faure frame `w = z² - z` (places `0, 1`), scaled local roots `z_0, z_1` with
`z_0(0) = 0`, `z_0 + z_1 = 1`, `z_0 z_1 = -θx`; `ρ = z_1 - z_0`; `k_c = 1/(ρ g_c)`.

* `lawD_zero`: the one-digit law `D(l)[c][c'] = δ_{cc'} - ∑_b M(0)[c][b] Ĝ_l[b][c']` (`prop:law`, `i = 0`).
* `faureG`, `faure_inv`: `G = M^{-1} = ((z_1 k_0, -z_0 k_1), (-k_0, k_1))`.
* **`gform`**: `D(l) = [x^l] 𝒟/(1-x)` with `𝒟 = I - M(0) G` =
  `((1 - g_0(0) z_1 k_0, g_0(0) z_0 k_1), (g_1(0) z_0 k_0, 1 - g_1(0) z_1 k_1))`, and `faure_z0`
  (`z_0 = -θx/z_1`), which turns the cross entries into the paper's `x · X_{c←c'}(x)` form.
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`prop:law` at depth `i = 0`** (the one-digit law): `D(l)[c][c'] = δ_{cc'} - ∑_b M(0)[c][b] Ĝ_l[b][c']`. -/
theorem lawD_zero {R : Type*} [CommRing R] {s : ℕ} (g zθ : Fin s → PowerSeries R)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (l : ℕ) (c c' : Fin s) :
    lawD g zθ G 0 l c c' = (if c = c' then 1 else 0) -
      ∑ b, constantCoeff (frameM g zθ c b) * coeff l (G b c' * PowerSeries.mk 1) := by
  simp [lawD, coeff_zero_eq_constantCoeff_apply]

section Faure

variable {F : Type*} [Field F]

/-- `M G = 1` for the Faure frame matrix `M = ((g_0, g_0 z_0), (g_1, g_1 z_1))`, `k_c ρ g_c = 1`. -/
theorem faure_inv (z0 z1 g0 g1 k0 k1 : PowerSeries F)
    (hk0 : k0 * ((z1 - z0) * g0) = 1) (hk1 : k1 * ((z1 - z0) * g1) = 1) :
    frameM ![g0, g1] ![z0, z1] * faureG z0 z1 k0 k1 = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [frameM, Matrix.mul_apply, Fin.sum_univ_two, faureG]
  · linear_combination hk0
  · ring
  · ring
  · linear_combination hk1

/-- **`lem:gform`** (one-digit law of a self-similar scramble of the Faure frame, in the multipliers):
`D(l)[c][c'] = [x^l] 𝒟[c][c']/(1-x)` with `𝒟 = I - M(0) G`, entry by entry. -/
theorem gform (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (l : ℕ) :
    lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 0 =
        coeff l ((1 - C (constantCoeff g0) * z1 * k0) * PowerSeries.mk 1) ∧
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 1 =
        coeff l (C (constantCoeff g0) * z0 * k1 * PowerSeries.mk 1) ∧
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        coeff l (C (constantCoeff g1) * z0 * k0 * PowerSeries.mk 1) ∧
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 =
        coeff l ((1 - C (constantCoeff g1) * z1 * k1) * PowerSeries.mk 1) := by
  have hz1 : constantCoeff z1 = 1 := by
    have := congrArg constantCoeff hsum
    rw [map_add, hz0, zero_add, map_one] at this
    exact this
  have hz0' : z0 = 1 - z1 := by rw [← hsum]; ring
  have hmk : coeff l (PowerSeries.mk (1 : ℕ → F)) = 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [lawD_zero, Fin.sum_univ_two, frameM, faureG, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, map_mul, hz0, hz1]
  · simp [sub_mul, map_sub, hmk, mul_assoc, coeff_C_mul]
  · simp [mul_assoc, coeff_C_mul, neg_mul]
  · rw [hz0']
    simp [sub_mul, mul_sub, map_sub, mul_assoc, coeff_C_mul, neg_mul]
    ring
  · rw [hz0']
    simp [sub_mul, mul_sub, map_sub, hmk, mul_assoc, coeff_C_mul]

/-- `z_0 = -θx / z_1` (the scaled local roots of the Faure frame, `z_0 z_1 = -θx`). -/
theorem faure_z0 (θ : F) (z0 z1 : PowerSeries F) (hz1 : constantCoeff z1 ≠ 0)
    (hprod : z0 * z1 = -(C θ * X)) : z0 = -(C θ * X) * z1⁻¹ := by
  rw [← hprod, mul_assoc, PowerSeries.mul_inv_cancel _ hz1, mul_one]

/-- All partial sums of `D` vanish iff `D = 0`. -/
theorem partial_sums_zero (D : PowerSeries F) :
    (∀ l, coeff l (D * PowerSeries.mk 1) = 0) ↔ D = 0 := by
  constructor
  · intro h
    have hall : D * PowerSeries.mk 1 = 0 := by ext l; rw [h l, map_zero]
    calc D = D * (PowerSeries.mk 1 * (1 - X)) := by rw [mk_one_mul_one_sub_eq_one, mul_one]
      _ = D * PowerSeries.mk 1 * (1 - X) := by ring
      _ = 0 := by rw [hall, zero_mul]
  · intro h l; rw [h, zero_mul, map_zero]

/-- **`prop:freeze` (a)**: for a self-similar scramble of the Faure frame, `O_1^{(l)} = 0` for all
`l ≥ 1` iff `g_1 = g_1(0) z_1/ρ`. -/
theorem freeze_a (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (hg1 : constantCoeff g1 ≠ 0) (hk1 : k1 * ((z1 - z0) * g1) = 1) :
    (∀ l, 1 ≤ l → lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 = 0) ↔
      g1 = C (constantCoeff g1) * z1 * (z1 - z0)⁻¹ := by
  have hz1 : constantCoeff z1 = 1 := by
    have := congrArg constantCoeff hsum
    rwa [map_add, hz0, zero_add, map_one] at this
  have hρ : constantCoeff (z1 - z0) = 1 := by rw [map_sub, hz0, hz1, sub_zero]
  have hri : (z1 - z0) * (z1 - z0)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [hρ]; exact one_ne_zero)
  have hk1c : constantCoeff k1 = (constantCoeff g1)⁻¹ := by
    have := congrArg constantCoeff hk1
    rw [map_mul, map_mul, hρ, one_mul, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  set Dser : PowerSeries F := 1 - C (constantCoeff g1) * z1 * k1 with hDser
  have hl : ∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 =
      coeff l (Dser * PowerSeries.mk 1) := fun l => (gform z0 z1 g0 g1 k0 k1 hz0 hsum l).2.2.2
  have hD0 : coeff 0 (Dser * PowerSeries.mk 1) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, hDser, map_sub, map_one, map_mul, map_mul,
      constantCoeff_C, hz1, hk1c, mul_one, mul_inv_cancel₀ hg1, sub_self, zero_mul]
  have key : (∀ l, 1 ≤ l → lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 = 0) ↔
      Dser = 0 := by
    rw [← partial_sums_zero]
    constructor
    · intro h l
      rcases l with _ | l
      · exact hD0
      · rw [← hl]; exact h (l + 1) (by omega)
    · intro h l _; rw [hl]; exact h l
  rw [key]
  constructor
  · intro h
    have h' : C (constantCoeff g1) * z1 * k1 = 1 := by linear_combination -h
    linear_combination (-g1) * h' - (C (constantCoeff g1) * z1 * k1 * g1) * hri +
      (C (constantCoeff g1) * z1 * (z1 - z0)⁻¹) * hk1
  · intro h
    rw [h] at hk1
    rw [hDser]
    linear_combination -hk1 + (C (constantCoeff g1) * z1 * k1) * hri

/-- **`prop:freeze` (b)**: for a self-similar scramble of the Faure frame with scale `θ ≠ 0` and
`g_1(0) ≠ 0`, `X_{1←0}^{(l)}` does not depend on `l ≥ 1` iff `g_0 = g_0(0)/(ρ z_1)`, and then
`X_{1←0}^{(l)} = -θ g_1(0)/g_0(0)` for all `l ≥ 1`. -/
theorem freeze_b (θ : F) (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (hprod : z0 * z1 = -(C θ * X)) (hθ : θ ≠ 0)
    (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0)
    (hk0 : k0 * ((z1 - z0) * g0) = 1) :
    ((∀ l, 1 ≤ l → lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 1 1 0) ↔
      g0 = C (constantCoeff g0) * ((z1 - z0) * z1)⁻¹) ∧
    (g0 = C (constantCoeff g0) * ((z1 - z0) * z1)⁻¹ → ∀ l, 1 ≤ l →
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        -(θ * constantCoeff g1 * (constantCoeff g0)⁻¹)) := by
  set c0 := constantCoeff g0 with hc0def
  set c1 := constantCoeff g1 with hc1def
  have hz1 : constantCoeff z1 = 1 := by
    have := congrArg constantCoeff hsum
    rwa [map_add, hz0, zero_add, map_one] at this
  have hρ : constantCoeff (z1 - z0) = 1 := by rw [map_sub, hz0, hz1, sub_zero]
  have hz1i : z1 * z1⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hz1]; exact one_ne_zero)
  have hw : (z1 - z0) * z1 * ((z1 - z0) * z1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [map_mul, hρ, hz1, one_mul]; exact one_ne_zero)
  have hc0 : C c0 * C c0⁻¹ = (1 : PowerSeries F) := by
    rw [← map_mul, mul_inv_cancel₀ hg0, map_one]
  have hθi : C θ * C θ⁻¹ = (1 : PowerSeries F) := by rw [← map_mul, mul_inv_cancel₀ hθ, map_one]
  have hc1i : C c1 * C c1⁻¹ = (1 : PowerSeries F) := by
    rw [← map_mul, mul_inv_cancel₀ hg1, map_one]
  have hk0c : constantCoeff k0 = c0⁻¹ := by
    have := congrArg constantCoeff hk0
    rw [map_mul, map_mul, hρ, one_mul, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  set Xs : PowerSeries F := -(C θ) * C c1 * k0 * z1⁻¹ with hXs
  set v : F := -(θ * c1 * c0⁻¹) with hv
  have hXs0 : constantCoeff Xs = v := by
    rw [hXs, map_mul, map_mul, map_mul, map_neg, constantCoeff_C, constantCoeff_C, hk0c,
      constantCoeff_inv, hz1, inv_one, mul_one, hv]; ring
  have hD : C c1 * z0 * k0 = X * Xs := by
    rw [faure_z0 θ z0 z1 (by rw [hz1]; exact one_ne_zero) hprod, hXs]; ring
  have hlX : ∀ n, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 (n + 1) 1 0 =
      coeff n (Xs * PowerSeries.mk 1) := by
    intro n
    rw [(gform z0 z1 g0 g1 k0 k1 hz0 hsum (n + 1)).2.2.1, hD, mul_assoc, coeff_succ_X_mul]
  have hS0 : coeff 0 (Xs * PowerSeries.mk 1) = v := by
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, hXs0]; simp
  -- step 1: independence of `l` ⟺ `Xs` is the constant `v`
  have step1 : (∀ l, 1 ≤ l → lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 1 1 0) ↔ Xs = C v := by
    rw [← sub_eq_zero, ← partial_sums_zero]
    have e : ∀ n, coeff n ((Xs - C v) * PowerSeries.mk 1) = coeff n (Xs * PowerSeries.mk 1) - v := by
      intro n; rw [sub_mul, map_sub, coeff_C_mul]; simp
    simp only [e, sub_eq_zero]
    constructor
    · intro h n
      have := h (n + 1) (by omega)
      rwa [hlX, hlX, hS0] at this
    · intro h l hl
      obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
      rw [hlX, hlX, h n, hS0]
  -- step 2: `Xs = v` ⟺ `k_0 = z_1/g_0(0)` ⟺ `g_0 = g_0(0)/(ρ z_1)`
  have stepA : Xs = C v ↔ k0 = C c0⁻¹ * z1 := by
    have eCv : (C v : PowerSeries F) = -(C θ * C c1 * C c0⁻¹) := by
      rw [hv, map_neg, map_mul, map_mul]
    rw [eCv, hXs]
    constructor
    · intro hX
      linear_combination (-(z1 * C θ⁻¹ * C c1⁻¹)) * hX -
        (z1 * (k0 * z1⁻¹ - C c0⁻¹) * C c1 * C c1⁻¹) * hθi - (z1 * (k0 * z1⁻¹ - C c0⁻¹)) * hc1i -
        k0 * hz1i
    · intro hK
      linear_combination (-(C θ * C c1 * z1⁻¹)) * hK - (C θ * C c1 * C c0⁻¹) * hz1i
  have stepB : k0 = C c0⁻¹ * z1 ↔ g0 = C c0 * ((z1 - z0) * z1)⁻¹ := by
    constructor
    · intro hK
      linear_combination (-g0) * hw + (((z1 - z0) * z1)⁻¹ * C c0) * hk0 -
        (((z1 - z0) * z1)⁻¹ * C c0 * (z1 - z0) * g0) * hK -
        (((z1 - z0) * z1)⁻¹ * g0 * (z1 - z0) * z1) * hc0
    · intro hg
      rw [hg] at hk0
      linear_combination (-k0) * hw + (z1 * C c0⁻¹) * hk0 -
        (k0 * (z1 - z0) * z1 * ((z1 - z0) * z1)⁻¹) * hc0
  refine ⟨step1.trans (stepA.trans stepB), fun hg l hl => ?_⟩
  have hX := stepA.2 (stepB.2 hg)
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [hlX, hX, coeff_C_mul]
  simp [hv]

end Faure

end GeoSeq
