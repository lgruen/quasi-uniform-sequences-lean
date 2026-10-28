/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.L3Defs
public import GeoSeq.Steer

@[expose] public section

/-!
# GeoSeq stage S9: the Kummer frame in dimension three and `prop:cover3`

* `cubeRt_cube`, `cubeRt_const`: `cubeRt a ³ = a`, `cubeRt a (0) = 1` (`a(0) = 1`, `3 ≠ 0`).
* `kum_inv`: the inverse of the frame matrix of the symmetric scramble,
  `G[b][c'] = 3⁻¹ ζ^{-bc'} τ^{-b} g⁻¹`.
* `kresp_add` (**depth direction**, `eq:steer3`): changing the free series `k = 1/g` by `x^m e` moves
  `(O^{(m)}, X_1^{(m+1)}, X_2^{(m+1)})` along `-e(0) g(0) (1, u_1, u_2)` and leaves the earlier partial
  sums unchanged.
* `steer3_step`, `steer3_exists`: the covering step and "the rule never stops" in dimension three.
* `kum_resp`: the responses of `kumGen p ζ θ g` (`prop:law` at depth `0` with `kum_inv`).
* **`cover3_step`, `cover3_exists`, `cover3_sep`, `cover3`** (`prop:cover3`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Cube roots -/

section Cube

variable {F : Type*} [Field F]

lemma cubeApprox_const (a : PowerSeries F) (n : ℕ) : constantCoeff (cubeApprox a n) = 1 := by
  induction n with
  | zero => simp [cubeApprox]
  | succ n ih => simp [cubeApprox, ih]

lemma cubeApprox_dvd (h3 : (3 : F) ≠ 0) (a : PowerSeries F) (ha : constantCoeff a = 1) (n : ℕ) :
    X ^ (n + 1) ∣ a - cubeApprox a n ^ 3 := by
  induction n with
  | zero =>
    rw [zero_add, pow_one, X_dvd_iff]
    simp [cubeApprox, ha]
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih
    have hA0 := cubeApprox_const a n
    have hc : coeff (n + 1) (a - cubeApprox a n ^ 3) = constantCoeff R := by
      rw [hR, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    show X ^ (n + 1 + 1) ∣ a - (cubeApprox a n +
      C (coeff (n + 1) (a - cubeApprox a n ^ 3) / 3) * X ^ (n + 1)) ^ 3
    rw [hc]
    set A := cubeApprox a n
    set c : F := constantCoeff R / 3
    have hY : X ∣ R - 3 * A ^ 2 * C c := by
      rw [X_dvd_iff]
      simp only [map_sub, map_mul, map_pow, hA0, constantCoeff_C, one_pow, mul_one, c]
      have : constantCoeff (3 : PowerSeries F) = 3 := map_ofNat _ 3
      rw [this]
      field_simp
      ring
    obtain ⟨Y, hY⟩ := hY
    refine ⟨Y - (3 * A * C c ^ 2 + C c ^ 3 * X ^ (n + 1)) * X ^ n, ?_⟩
    linear_combination hR + X ^ (n + 1) * hY

lemma cubeApprox_coeff (a : PowerSeries F) (j n : ℕ) (hj : j ≤ n) :
    ∀ m, n ≤ m → coeff j (cubeApprox a m) = coeff j (cubeApprox a n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [cubeApprox, map_add, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, add_zero, ih]

lemma cubeRt_eq (a : PowerSeries F) (n : ℕ) : ∃ e, cubeRt a = cubeApprox a n + X ^ (n + 1) * e := by
  have : X ^ (n + 1) ∣ cubeRt a - cubeApprox a n := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, cubeRt, coeff_mk, cubeApprox_coeff a j j le_rfl n (by omega), sub_self]
  obtain ⟨e, he⟩ := this
  exact ⟨e, by rw [← he]; ring⟩

/-- The cube root has constant term `1`. -/
theorem cubeRt_const (a : PowerSeries F) : constantCoeff (cubeRt a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, cubeRt, coeff_mk, coeff_zero_eq_constantCoeff_apply,
    cubeApprox_const]

/-- **`cubeRt a ³ = a`** for `a(0) = 1` in characteristic `≠ 3`. -/
theorem cubeRt_cube (h3 : (3 : F) ≠ 0) (a : PowerSeries F) (ha : constantCoeff a = 1) :
    cubeRt a ^ 3 = a := by
  ext n
  obtain ⟨e, he⟩ := cubeRt_eq a n
  obtain ⟨R, hR⟩ := cubeApprox_dvd h3 a ha n
  have : cubeRt a ^ 3 - a = X ^ (n + 1) *
      (3 * cubeApprox a n ^ 2 * e + 3 * cubeApprox a n * X ^ (n + 1) * e ^ 2 +
        X ^ (2 * (n + 1)) * e ^ 3 - R) := by
    rw [he]; linear_combination -hR
  have h := congrArg (coeff n) this
  rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at h
  exact sub_eq_zero.mp h

end Cube

/-! ## Steering one column in dimension three (`eq:steer3`) -/

section Column3

variable {F : Type*} [Field F]

lemma coeff1_mul (φ ψ : PowerSeries F) :
    coeff 1 (φ * ψ) = constantCoeff φ * coeff 1 ψ + coeff 1 φ * constantCoeff ψ := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp [coeff_zero_eq_constantCoeff_apply]

/-- Changing the free series `k` by `x^m e` changes the partial sum `n` by `[x^{n-m}] E e/(1-x)`
(only for `n ≥ m`). -/
lemma kresp_add (δ : F) (E k e : PowerSeries F) (m n : ℕ) :
    kresp δ E (k + X ^ m * e) n =
      kresp δ E k n - (if m ≤ n then coeff (n - m) (E * e * PowerSeries.mk 1) else 0) := by
  unfold kresp
  rw [← coeff_X_pow_mul', ← map_sub]
  congr 1
  ring

/-- **Depth direction, own part**: `O^{(m)}` moves by `-E(0) e(0)`. -/
lemma kresp_own (δ : F) (E k e : PowerSeries F) (m : ℕ) :
    kresp δ E (k + X ^ m * e) m = kresp δ E k m - constantCoeff E * constantCoeff e := by
  rw [kresp_add, if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  simp

/-- **Depth direction, cross part** (`E(0) = 0`): `X^{(n)}`, `n ≤ m`, is unchanged and `X^{(m+1)}`
moves by `-[x]E · e(0)`. -/
lemma kresp_cross (δ : F) (E k e : PowerSeries F) (hE : constantCoeff E = 0) (m : ℕ) :
    (∀ n, n ≤ m → kresp δ E (k + X ^ m * e) n = kresp δ E k n) ∧
    kresp δ E (k + X ^ m * e) (m + 1) = kresp δ E k (m + 1) - coeff 1 E * constantCoeff e := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [kresp_add]
    rcases Nat.lt_or_ge n m with h | h
    · rw [if_neg (by omega), sub_zero]
    · obtain rfl : n = m := le_antisymm hn h
      rw [if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
      simp [hE]
  · rw [kresp_add, if_pos (by omega), show m + 1 - m = 1 by omega, coeff1_mul, coeff1_mul]
    simp [hE]

/-- `X^{(1)} = δ - [x]E · k(0)` for `E(0) = 0`. -/
lemma kresp_one (δ : F) (E k : PowerSeries F) (hE : constantCoeff E = 0) :
    kresp δ E k 1 = δ - coeff 1 E * constantCoeff k := by
  unfold kresp
  rw [sub_mul, map_sub, coeff1_mul, coeff1_mul, coeff1_mul]
  simp [hE]

/-- **The covering step** (condition (ii) of `prop:cover3`): for every free series `k` (every history)
and every depth `m`, some value `t` of the coefficient `m` puts `(O^{(m)}, X_1^{(m+1)}, X_2^{(m+1)})`
into `W 0 × W 1 × W 2`. -/
theorem steer3_step (E : Fin 3 → PowerSeries F) (a u1 u2 : F) (ha : a ≠ 0)
    (hE0 : constantCoeff (E 0) = a) (hE1 : constantCoeff (E 1) = 0) (hE2 : constantCoeff (E 2) = 0)
    (hu1 : coeff 1 (E 1) = a * u1) (hu2 : coeff 1 (E 2) = a * u2)
    (W : Fin 3 → Set F) (hcov : Covers3 u1 u2 W) (k : PowerSeries F) (m : ℕ) :
    ∃ t : F, kresp 1 (E 0) (k + X ^ m * C t) m ∈ W 0 ∧
      kresp 0 (E 1) (k + X ^ m * C t) (m + 1) ∈ W 1 ∧
      kresp 0 (E 2) (k + X ^ m * C t) (m + 1) ∈ W 2 := by
  obtain ⟨s, h0, h1, h2⟩ := hcov ![kresp 1 (E 0) k m, kresp 0 (E 1) k (m + 1), kresp 0 (E 2) k (m + 1)]
  have e0 : (![kresp 1 (E 0) k m, kresp 0 (E 1) k (m + 1), kresp 0 (E 2) k (m + 1)] : Fin 3 → F) 0 =
    kresp 1 (E 0) k m := rfl
  have e1 : (![kresp 1 (E 0) k m, kresp 0 (E 1) k (m + 1), kresp 0 (E 2) k (m + 1)] : Fin 3 → F) 1 =
    kresp 0 (E 1) k (m + 1) := rfl
  have e2 : (![kresp 1 (E 0) k m, kresp 0 (E 1) k (m + 1), kresp 0 (E 2) k (m + 1)] : Fin 3 → F) 2 =
    kresp 0 (E 2) k (m + 1) := rfl
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
  refine ⟨-s / a, ?_, ?_, ?_⟩
  · rw [kresp_own, constantCoeff_C, hE0]
    convert h0 using 1
    field_simp
    ring
  · rw [(kresp_cross 0 (E 1) k _ hE1 m).2, constantCoeff_C, hu1]
    convert h1 using 1
    field_simp
    ring
  · rw [(kresp_cross 0 (E 2) k _ hE2 m).2, constantCoeff_C, hu2]
    convert h2 using 1
    field_simp
    ring

/-- **The rule never stops** (dimension three): under (i) `-u_d ∈ W d` and (ii) there is a free series
`k` with `k(0) = a⁻¹` all of whose partial sums `O^{(l)}`, `X_1^{(l)}`, `X_2^{(l)}` (`l ≥ 1`) lie in their
windows. -/
theorem steer3_exists (E : Fin 3 → PowerSeries F) (a u1 u2 : F) (ha : a ≠ 0)
    (hE0 : constantCoeff (E 0) = a) (hE1 : constantCoeff (E 1) = 0) (hE2 : constantCoeff (E 2) = 0)
    (hu1 : coeff 1 (E 1) = a * u1) (hu2 : coeff 1 (E 2) = a * u2)
    (W : Fin 3 → Set F) (hi1 : -u1 ∈ W 1) (hi2 : -u2 ∈ W 2) (hcov : Covers3 u1 u2 W) :
    ∃ k : PowerSeries F, constantCoeff k = a⁻¹ ∧ ∀ l, 1 ≤ l →
      kresp 1 (E 0) k l ∈ W 0 ∧ kresp 0 (E 1) k l ∈ W 1 ∧ kresp 0 (E 2) k l ∈ W 2 := by
  classical
  let choose : ℕ → PowerSeries F → F := fun m k =>
    Classical.choose (steer3_step E a u1 u2 ha hE0 hE1 hE2 hu1 hu2 W hcov k m)
  have hchoose : ∀ m k, kresp 1 (E 0) (k + X ^ m * C (choose m k)) m ∈ W 0 ∧
      kresp 0 (E 1) (k + X ^ m * C (choose m k)) (m + 1) ∈ W 1 ∧
      kresp 0 (E 2) (k + X ^ m * C (choose m k)) (m + 1) ∈ W 2 := fun m k =>
    Classical.choose_spec (steer3_step E a u1 u2 ha hE0 hE1 hE2 hu1 hu2 W hcov k m)
  set ap := steerApprox choose (C a⁻¹)
  let k : PowerSeries F := PowerSeries.mk fun n => coeff n (ap n)
  have hdvd : ∀ n, ∃ e, k = ap n + X ^ (n + 1) * e := by
    intro n
    have : X ^ (n + 1) ∣ k - ap n := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, coeff_mk, steerApprox_coeff choose _ j j le_rfl n (by omega), sub_self]
    obtain ⟨e, he⟩ := this
    exact ⟨e, by rw [← he]; ring⟩
  have hk0 : constantCoeff k = a⁻¹ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    show coeff 0 (C a⁻¹) = a⁻¹
    rw [coeff_zero_C]
  refine ⟨k, hk0, fun l hl => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨e, he⟩ := hdvd l
    have h1 := kresp_add 1 (E 0) (ap l) e (l + 1) l
    rw [if_neg (by omega), sub_zero, ← he] at h1
    rw [h1]
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact (hchoose (m + 1) (ap m)).1
  all_goals
    rcases Nat.lt_or_ge l 2 with hl2 | hl2
    · obtain rfl : l = 1 := by omega
      first
      | (rw [kresp_one 0 _ k hE1, hk0, hu1]; convert hi1 using 1; field_simp; ring)
      | (rw [kresp_one 0 _ k hE2, hk0, hu2]; convert hi2 using 1; field_simp; ring)
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 + 1 := ⟨l - 2, by omega⟩
      obtain ⟨e, he⟩ := hdvd (m + 1)
      first
      | (have h1 := (kresp_cross 0 (E 1) (ap (m + 1)) e hE1 (m + 1 + 1)).1 (m + 1 + 1) le_rfl
         rw [← he] at h1; rw [h1]; exact (hchoose (m + 1) (ap m)).2.1)
      | (have h1 := (kresp_cross 0 (E 2) (ap (m + 1)) e hE2 (m + 1 + 1)).1 (m + 1 + 1) le_rfl
         rw [← he] at h1; rw [h1]; exact (hchoose (m + 1) (ap m)).2.2)

end Column3

/-! ## The Kummer frame over a field (`w = z³ - 1`, places `1, ζ, ζ²`) -/

section KumAlg

variable {F : Type*} [Field F]

lemma zeta3 (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ

lemma zeta_ne_zero (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ 0 := by
  rintro rfl; simp at hζ

lemma zeta_ne_one (h3 : (3 : F) ≠ 0) (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ 1 := by
  rintro rfl; apply h3; linear_combination hζ

lemma zeta_sq_ne_one (h3 : (3 : F) ≠ 0) (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 2 ≠ 1 := by
  intro h
  apply zeta_ne_one h3 ζ hζ
  linear_combination zeta3 ζ hζ - ζ * h

lemma zeta_ne_sq (h3 : (3 : F) ≠ 0) (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ ζ ^ 2 := by
  intro h
  apply zeta_ne_one h3 ζ hζ
  have : ζ * (ζ - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (zeta_ne_zero ζ hζ)
  · linear_combination h0

lemma zpow_mod3 (ζ : F) (hζ3 : ζ ^ 3 = 1) (n : ℕ) : ζ ^ n = ζ ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hζ3, one_pow, mul_one]

lemma fin3_sub_val (c c' : Fin 3) : ((c - c' : Fin 3) : ℕ) = ((c : ℕ) + 2 * c') % 3 := by
  fin_cases c <;> fin_cases c' <;> rfl

/-- `ζ^{cb} ζ^{2bc'} = (ζ^{c - c'})^b`. -/
lemma zeta_prod (ζ : F) (hζ3 : ζ ^ 3 = 1) (c c' : Fin 3) (b : ℕ) :
    ζ ^ ((c : ℕ) * b) * ζ ^ (2 * b * (c' : ℕ)) = (ζ ^ ((c - c' : Fin 3) : ℕ)) ^ b := by
  rw [fin3_sub_val, ← zpow_mod3 ζ hζ3, ← pow_add, ← pow_mul]
  congr 1; ring

/-- `1 + r + r² = 3` for `r = ζ^0` and `0` for `r = ζ, ζ²`. -/
lemma zeta_sum (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) (d : Fin 3) :
    1 + ζ ^ (d : ℕ) + (ζ ^ (d : ℕ)) ^ 2 = if d = 0 then 3 else 0 := by
  fin_cases d
  · simp; norm_num
  · simp; linear_combination hζ
  · simp; linear_combination (ζ ^ 2 - ζ + 1) * hζ

lemma tau_coeff1 (h3 : (3 : F) ≠ 0) (θ : F) (τ : PowerSeries F) (hτ0 : constantCoeff τ = 1)
    (hτ3 : τ ^ 3 = 1 + C θ * X) : coeff 1 τ = θ / 3 := by
  have h := congrArg (coeff 1) hτ3
  rw [pow_succ, coeff1_mul, pow_two, coeff1_mul, map_mul, hτ0] at h
  simp at h
  field_simp
  linear_combination h

lemma tauinv_facts (h3 : (3 : F) ≠ 0) (θ : F) (τ : PowerSeries F) (hτ0 : constantCoeff τ = 1)
    (hτ3 : τ ^ 3 = 1 + C θ * X) :
    τ * τ⁻¹ = 1 ∧ constantCoeff τ⁻¹ = 1 ∧ coeff 1 τ⁻¹ = -(θ / 3) := by
  have hm : τ * τ⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hτ0]; exact one_ne_zero)
  have hc : constantCoeff τ⁻¹ = 1 := by rw [constantCoeff_inv, hτ0, inv_one]
  refine ⟨hm, hc, ?_⟩
  have h := congrArg (coeff 1) hm
  rw [coeff1_mul, hτ0, hc, tau_coeff1 h3 θ τ hτ0 hτ3] at h
  simp at h
  linear_combination h

/-- The response series `E_d = (a/3) Σ_{ζ^d}`: `E_0(0) = a`, `E_d(0) = 0` and `[x]E_d = a u_d` for
`d = 1, 2`. -/
lemma kumE_facts (h3 : (3 : F) ≠ 0) (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) (θ : F) (τ : PowerSeries F)
    (hτ0 : constantCoeff τ = 1) (hτ3 : τ ^ 3 = 1 + C θ * X) (a : F) :
    constantCoeff (C (a / 3) * sig τ (ζ ^ ((0 : Fin 3) : ℕ))) = a ∧
    constantCoeff (C (a / 3) * sig τ (ζ ^ ((1 : Fin 3) : ℕ))) = 0 ∧
    constantCoeff (C (a / 3) * sig τ (ζ ^ ((2 : Fin 3) : ℕ))) = 0 ∧
    coeff 1 (C (a / 3) * sig τ (ζ ^ ((1 : Fin 3) : ℕ))) = a * kumU ζ θ 1 ∧
    coeff 1 (C (a / 3) * sig τ (ζ ^ ((2 : Fin 3) : ℕ))) = a * kumU ζ θ 2 := by
  obtain ⟨-, hc, h1⟩ := tauinv_facts h3 θ τ hτ0 hτ3
  have hcs : ∀ r : F, constantCoeff (sig τ r) = 1 + r + r ^ 2 := by
    intro r; simp [sig, hc, hτ0]
  have h1s : ∀ r : F, coeff 1 (sig τ r) = -(θ / 3) * (r + 2 * r ^ 2) := by
    intro r
    simp only [sig, map_add, coeff_C_mul, coeff_one, pow_two τ⁻¹, coeff1_mul, hc, h1]
    simp
    ring
  have hz1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr (zeta_ne_one h3 ζ hζ).symm
  have hz2 : 1 - ζ ^ 2 ≠ 0 := sub_ne_zero.mpr (zeta_sq_ne_one h3 ζ hζ).symm
  have e0 := zeta_sum ζ hζ 0
  have e1 := zeta_sum ζ hζ 1
  have e2 := zeta_sum ζ hζ 2
  simp only [Fin.isValue, if_true, show ((1 : Fin 3) = 0) = False by decide,
    show ((2 : Fin 3) = 0) = False by decide, if_false] at e0 e1 e2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, constantCoeff_C, hcs, e0]; field_simp
  · rw [map_mul, constantCoeff_C, hcs, e1, mul_zero]
  · rw [map_mul, constantCoeff_C, hcs, e2, mul_zero]
  · rw [coeff_C_mul, h1s, kumU]
    simp only [Fin.val_one, pow_one]
    field_simp
    linear_combination (-(a * θ) * (3 - 2 * ζ)) * hζ
  · rw [coeff_C_mul, h1s, kumU]
    simp only [Fin.val_two]
    field_simp
    linear_combination (-(a * θ) * (-2 * ζ ^ 4 + 2 * ζ ^ 3 + ζ ^ 2 - 3 * ζ + 3)) * hζ

/-- The inverse of the frame matrix of the symmetric Kummer scramble:
`G[b][c'] = 3⁻¹ ζ^{2bc'} τ^{-b} g⁻¹` (`ζ^{2bc'} = ζ^{-bc'}`). -/
theorem kum_inv (h3 : (3 : F) ≠ 0) (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) (τ g : PowerSeries F)
    (hτ0 : constantCoeff τ = 1) (hg : constantCoeff g ≠ 0) :
    frameM (fun _ => g) (fun c : Fin 3 => C (ζ ^ (c : ℕ)) * τ) *
      Matrix.of (fun b c' : Fin 3 => C ((3 : F)⁻¹ * ζ ^ (2 * (b : ℕ) * c')) * τ⁻¹ ^ (b : ℕ) * g⁻¹) = 1 := by
  have hgg : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hg
  have hττ : τ * τ⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hτ0]; exact one_ne_zero)
  have hζ3 := zeta3 ζ hζ
  have hterm : ∀ (c c' b : Fin 3), g * (C (ζ ^ (c : ℕ)) * τ) ^ (b : ℕ) *
      (C ((3 : F)⁻¹ * ζ ^ (2 * (b : ℕ) * c')) * τ⁻¹ ^ (b : ℕ) * g⁻¹) =
      C ((3 : F)⁻¹ * (ζ ^ ((c - c' : Fin 3) : ℕ)) ^ (b : ℕ)) := by
    intro c c' b
    rw [← zeta_prod ζ hζ3 c c' b]
    calc g * (C (ζ ^ (c : ℕ)) * τ) ^ (b : ℕ) *
          (C ((3 : F)⁻¹ * ζ ^ (2 * (b : ℕ) * c')) * τ⁻¹ ^ (b : ℕ) * g⁻¹)
        = C ((3 : F)⁻¹ * (ζ ^ ((c : ℕ) * b) * ζ ^ (2 * (b : ℕ) * c'))) * (g * g⁻¹) *
            (τ * τ⁻¹) ^ (b : ℕ) := by
          rw [mul_pow, ← map_pow, ← pow_mul]; simp only [map_mul]; ring
      _ = _ := by rw [hgg, hττ, one_pow, mul_one, mul_one]
  ext1 c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [frameM, Matrix.of_apply]
  rw [Fin.sum_univ_three, hterm, hterm, hterm, ← map_add, ← map_add]
  have hs := zeta_sum ζ hζ (c - c')
  have : (3 : F)⁻¹ * (ζ ^ ((c - c' : Fin 3) : ℕ)) ^ ((0 : Fin 3) : ℕ) +
      (3 : F)⁻¹ * (ζ ^ ((c - c' : Fin 3) : ℕ)) ^ ((1 : Fin 3) : ℕ) +
      (3 : F)⁻¹ * (ζ ^ ((c - c' : Fin 3) : ℕ)) ^ ((2 : Fin 3) : ℕ) = if c = c' then 1 else 0 := by
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    rw [← mul_add, ← mul_add, hs]
    by_cases h : c = c'
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h]; field_simp
    · rw [if_neg (fun h' => h (sub_eq_zero.mp h')), if_neg h, mul_zero]
  rw [this]
  split_ifs <;> simp


/-- **The responses of the symmetric Kummer scramble** (`prop:law` at depth `0` with `kum_inv`):
`D(l)[c][c'] = [x^l] (δ_{cc'} - (g(0)/3) Σ_{ζ^{c-c'}} g⁻¹)/(1 - x)` at every level `K ≥ l ≥ 1`. -/
theorem kum_resp_alg [Fintype F] [DecidableEq F] (h3 : (3 : F) ≠ 0) (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (θ : F) (hθ : θ ≠ 0) (τ : PowerSeries F) (hτ0 : constantCoeff τ = 1)
    (hτ3 : τ ^ 3 = 1 + C θ * X) (g : PowerSeries F) (hg : constantCoeff g ≠ 0) (K l : ℕ)
    (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 3) :
    IsCarryEntry (ssGen (fun _ => g) (fun c : Fin 3 => C (ζ ^ (c : ℕ)) * τ)) K 0 l c c'
      (kresp (if c = c' then 1 else 0)
        (C (constantCoeff g / 3) * sig τ (ζ ^ ((c - c' : Fin 3) : ℕ))) g⁻¹ l) := by
  have hζ3 := zeta3 ζ hζ
  have hMG := kum_inv h3 ζ hζ τ g hτ0 hg
  have hdeg : (Polynomial.X ^ 3 - 1 : Polynomial F).natDegree ≤ 3 :=
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hroot : ∀ c : Fin 3, Polynomial.aeval (C (ζ ^ (c : ℕ)) * τ)
      (Polynomial.X ^ 3 - 1 : Polynomial F) = C θ * X := by
    intro c
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one]
    rw [mul_pow, hτ3, show (C (ζ ^ (c : ℕ)) : PowerSeries F) ^ 3 = 1 by
      rw [← map_pow, ← pow_mul, mul_comm (c : ℕ) 3, pow_mul, hζ3, one_pow, map_one]]
    ring
  have hlaw := law (fun _ => g) (fun c : Fin 3 => C (ζ ^ (c : ℕ)) * τ) _ hdeg θ θ⁻¹
    (mul_inv_cancel₀ hθ) hroot _ hMG K 0 l hl hlK c c'
  rw [lawD_zero] at hlaw
  convert hlaw using 1
  unfold kresp
  rw [sub_mul, map_sub, coeff_C_mul, coeff_mk, Pi.one_apply, mul_one]
  congr 1
  have hcc : ∀ b : Fin 3, constantCoeff (frameM (fun _ : Fin 3 => g) (fun c : Fin 3 => C (ζ ^ (c : ℕ)) * τ) c b) =
      constantCoeff g * ζ ^ ((c : ℕ) * b) := by
    intro b
    simp only [frameM, map_mul, map_pow, constantCoeff_C, hτ0, mul_one, ← pow_mul]
  simp only [hcc, Matrix.of_apply]
  simp only [← coeff_C_mul, ← map_sum]
  congr 1
  rw [Fin.sum_univ_three]
  have hz : ∀ b : Fin 3, C (constantCoeff g * ζ ^ ((c : ℕ) * b)) *
      (C ((3 : F)⁻¹ * ζ ^ (2 * (b : ℕ) * c')) * τ⁻¹ ^ (b : ℕ) * g⁻¹ * PowerSeries.mk 1) =
      C (constantCoeff g / 3) * C ((ζ ^ ((c - c' : Fin 3) : ℕ)) ^ (b : ℕ)) * τ⁻¹ ^ (b : ℕ) *
        g⁻¹ * PowerSeries.mk 1 := by
    intro b
    rw [← zeta_prod ζ hζ3 c c' b]
    simp only [map_mul, div_eq_mul_inv]
    ring
  rw [hz, hz, hz]
  simp only [sig, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, map_one]
  ring

end KumAlg

/-! ## `prop:cover3` over `𝔽_p` -/

section Cover3

lemma three_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp h2
  omega

lemma five_le_of_mod3 (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 3 = 1) : 5 ≤ p := by
  have h2 := hp.out.two_le
  by_contra h
  interval_cases p
  · omega
  · omega
  · exact absurd hp.out (by decide)

/-- `τ = kumTau p θ`: `τ(0) = 1`, `τ³ = 1 + θx`. -/
theorem kumTau_facts (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) (θ : ZMod p) :
    constantCoeff (kumTau p θ) = 1 ∧ kumTau p θ ^ 3 = 1 + C θ * X :=
  ⟨cubeRt_const _, cubeRt_cube (three_ne_zero_zmod p hp3) _ (by simp)⟩

/-- **The responses of `kumGen p ζ θ g`** (`prop:law` + `kum_inv`): with the free series `g⁻¹`,
`D(l)[c][c'] = [x^l] (δ_{cc'} - (g(0)/3)(1 + r τ⁻¹ + r² τ⁻²) g⁻¹)/(1 - x)`, `r = ζ^{c - c'}`. -/
theorem kum_resp (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) (ζ θ : ZMod p) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hθ : θ ≠ 0) (g : PowerSeries (ZMod p)) (hg : constantCoeff g ≠ 0) (K l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) (c c' : Fin 3) :
    IsCarryEntry (kumGen p ζ θ g) K 0 l c c'
      (kresp (if c = c' then 1 else 0)
        (C (constantCoeff g / 3) * sig (kumTau p θ) (ζ ^ ((c - c' : Fin 3) : ℕ))) g⁻¹ l) :=
  kum_resp_alg (three_ne_zero_zmod p hp3) ζ hζ θ hθ _ (kumTau_facts p hp3 θ).1
    (kumTau_facts p hp3 θ).2 g hg K l hl hlK c c'

/-- The certificate half of `prop:cover3` (`lem:cert`, `j = 1`): a `(0,3)`-sequence over `𝔽_p`
whose one-digit responses lie in the windows has `c(P_{3K}) ≥ min(1, LB)` for every `K ≥ 1`. -/
theorem cer3 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (C : Gen 3 (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (W : Fin 3 → Set (ZMod p)) (hW : RespIn3 C W) (LB : ℝ) (hLB : C3bound p W LB) (K : ℕ)
    (hK : 1 ≤ K) : SepAtLevel p 3 K (seqPoint (zcode p) C) (min 1 LB) := by
  have hnet : BlockNet0 (zcode p) C (3 * K) 0 := hseq (3 * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  classical
  let Dr : ℕ → Fin 3 → Fin 3 → ZMod p := fun l c c' =>
    if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists (zcode p) C K hnet 0 l c c')
    else 0
  have hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c') := by
    intro l h1 h2 c c'
    simp only [Dr, And.intro h1 h2, and_self, dite_true]
    exact Classical.choose_spec (carry_exists (zcode p) C K hnet 0 l c c')
  refine cert_one C K hq hnet Dr hD LB ?_
  rintro e l ⟨he, hne, hl⟩
  exact hLB e he hne (fun c c' => Dr (l c') c c')
    (fun c c' => hW K (l c') (hl c').1 (hl c').2 c c' _ (hD _ (hl c').1 (hl c').2 c c'))

lemma win_pick {F : Type*} [Field F] (E : Fin 3 → PowerSeries F) (k : PowerSeries F) (l : ℕ)
    (W : Fin 3 → Set F)
    (h : kresp 1 (E 0) k l ∈ W 0 ∧ kresp 0 (E 1) k l ∈ W 1 ∧ kresp 0 (E 2) k l ∈ W 2)
    (c c' : Fin 3) : kresp (if c = c' then 1 else 0) (E (c - c')) k l ∈ W (c - c') := by
  obtain ⟨h0, h1, h2⟩ := h
  fin_cases c <;> fin_cases c' <;> simpa using (by assumption)

lemma ps_inv_inv1 {F : Type*} [Field F] (k : PowerSeries F) (hk : constantCoeff k ≠ 0) :
    (k⁻¹)⁻¹ = k := by
  have := ps_inv_inv 1 k (by simp) hk
  simpa using this

/-- **`prop:cover3`, the choices exist at every depth for every history**: for every multiplier `g`
(`g(0) ≠ 0`) and depth `l ≥ 1` there is `g'` agreeing with `g` in the coefficients `< l` whose depth-`l`
own responses and depth-`(l+1)` cross responses lie in the windows (at every level). -/
theorem cover3_step (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) (ζ θ : ZMod p)
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hθ : θ ≠ 0) (W : Fin 3 → Set (ZMod p))
    (hcov : Covers3 (kumU ζ θ 1) (kumU ζ θ 2) W) (g : PowerSeries (ZMod p))
    (hg : constantCoeff g ≠ 0) (l : ℕ) (hl : 1 ≤ l) :
    ∃ g' : PowerSeries (ZMod p), (∀ j < l, coeff j g' = coeff j g) ∧
      (∀ K, l ≤ K → ∀ c : Fin 3, ∀ d, IsCarryEntry (kumGen p ζ θ g') K 0 l c c d → d ∈ W 0) ∧
      (∀ K, l + 1 ≤ K → ∀ c c' : Fin 3, ∀ d, c ≠ c' →
        IsCarryEntry (kumGen p ζ θ g') K 0 (l + 1) c c' d → d ∈ W (c - c')) := by
  have h3 := three_ne_zero_zmod p hp3
  obtain ⟨hτ0, hτ3⟩ := kumTau_facts p hp3 θ
  set a := constantCoeff g
  obtain ⟨e0, e1, e2, u1, u2⟩ := kumE_facts h3 ζ hζ θ (kumTau p θ) hτ0 hτ3 a
  set E : Fin 3 → PowerSeries (ZMod p) := fun d => C (a / 3) * sig (kumTau p θ) (ζ ^ (d : ℕ))
  obtain ⟨t, ht0, ht1, ht2⟩ := steer3_step E a _ _ hg e0 e1 e2 u1 u2 W hcov g⁻¹ l
  set k' := g⁻¹ + X ^ l * C t
  have hk0 : constantCoeff g⁻¹ ≠ 0 := by rw [constantCoeff_inv]; exact inv_ne_zero hg
  obtain ⟨f, hf⟩ := ps_inv_add 1 g⁻¹ (C t) l hl (by simp) hk0
  simp only [one_mul, ps_inv_inv1 g hg] at hf
  have hk'0 : constantCoeff k' = constantCoeff g⁻¹ := by
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    simp [k', pow_succ]
  have hk'ne : constantCoeff k' ≠ 0 := by rw [hk'0]; exact hk0
  have hcoef : ∀ j < l, coeff j k'⁻¹ = coeff j g := by
    intro j hj
    rw [hf, map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]
  have hcc : constantCoeff k'⁻¹ = a := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoef 0 hl, coeff_zero_eq_constantCoeff_apply]
  have hg' : constantCoeff k'⁻¹ ≠ 0 := by rw [hcc]; exact hg
  refine ⟨k'⁻¹, hcoef, fun K hK c d hd => ?_, fun K hK c c' d hcc' hd => ?_⟩
  · have hr := kum_resp p hp3 ζ θ hζ hθ k'⁻¹ hg' K l hl hK c c
    rw [ps_inv_inv1 k' hk'ne, hcc, if_pos rfl, sub_self] at hr
    rw [carryEntry_unique _ _ _ _ _ _ hd hr]
    exact ht0
  · have hr := kum_resp p hp3 ζ θ hζ hθ k'⁻¹ hg' K (l + 1) (by omega) hK c c'
    rw [ps_inv_inv1 k' hk'ne, hcc, if_neg hcc'] at hr
    rw [carryEntry_unique _ _ _ _ _ _ hd hr]
    have hne : c - c' ≠ 0 := fun h => hcc' (sub_eq_zero.mp h)
    generalize c - c' = d' at hne ⊢
    fin_cases d'
    · exact absurd rfl hne
    · exact ht1
    · exact ht2

/-- **`prop:cover3`, existence**: under (i) and (ii) there is a multiplier `g` (`g(0) = 1`, the choice
`ψ_0 = 1`) all of whose responses lie in the windows at every level. -/
theorem cover3_exists (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) (ζ θ : ZMod p)
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hθ : θ ≠ 0) (W : Fin 3 → Set (ZMod p))
    (hi1 : -kumU ζ θ 1 ∈ W 1) (hi2 : -kumU ζ θ 2 ∈ W 2)
    (hcov : Covers3 (kumU ζ θ 1) (kumU ζ θ 2) W) :
    ∃ g : PowerSeries (ZMod p), constantCoeff g = 1 ∧ RespIn3 (kumGen p ζ θ g) W := by
  have h3 := three_ne_zero_zmod p hp3
  obtain ⟨hτ0, hτ3⟩ := kumTau_facts p hp3 θ
  obtain ⟨e0, e1, e2, u1, u2⟩ := kumE_facts h3 ζ hζ θ (kumTau p θ) hτ0 hτ3 1
  set E : Fin 3 → PowerSeries (ZMod p) := fun d => C (1 / 3) * sig (kumTau p θ) (ζ ^ (d : ℕ))
  obtain ⟨k, hk0, hk⟩ := steer3_exists E 1 _ _ one_ne_zero e0 e1 e2 u1 u2 W hi1 hi2 hcov
  rw [inv_one] at hk0
  have hkne : constantCoeff k ≠ 0 := by rw [hk0]; exact one_ne_zero
  have hg0 : constantCoeff k⁻¹ = 1 := by rw [constantCoeff_inv, hk0, inv_one]
  refine ⟨k⁻¹, hg0, fun K l hl hlK c c' d hd => ?_⟩
  have hr := kum_resp p hp3 ζ θ hζ hθ k⁻¹ (by rw [hg0]; exact one_ne_zero) K l hl hlK c c'
  rw [ps_inv_inv1 k hkne, hg0] at hr
  rw [carryEntry_unique _ _ _ _ _ _ hd hr]
  exact win_pick E k l W (hk l hl) c c'

/-- **`prop:cover3`, every choice**: a symmetric Kummer scramble with scale `θ ≠ 0` and multiplier `g`
(`g(0) ≠ 0`) whose responses lie in the windows is a `(0,3)`-sequence (every prefix `P_m` is a
`(0,m,3)`-net), and `c(P_{3K}) ≥ min(1, LB)` for every `K ≥ 1` and every `LB` below the certificate value
`LB(W_o, W_1, W_2)`. -/
theorem cover3_sep (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) (ζ θ : ZMod p)
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hθ : θ ≠ 0) (W : Fin 3 → Set (ZMod p)) (g : PowerSeries (ZMod p))
    (hg : constantCoeff g ≠ 0) (hW : RespIn3 (kumGen p ζ θ g) W) :
    IsSeq0 (zcode p) (kumGen p ζ θ g) ∧
      ∀ LB : ℝ, C3bound p W LB → ∀ K, 1 ≤ K →
        SepAtLevel p 3 K (seqPoint (zcode p) (kumGen p ζ θ g)) (min 1 LB) := by
  have h3 := three_ne_zero_zmod p hp3
  have hp5 := five_le_of_mod3 p hp3
  obtain ⟨hτ0, hτ3⟩ := kumTau_facts p hp3 θ
  have hτ1 := tau_coeff1 h3 θ (kumTau p θ) hτ0 hτ3
  have hseq : IsSeq0 (zcode p) (kumGen p ζ θ g) := by
    refine ss_t0 (zcode p) _ _ ?_ (fun _ => hg) ?_
    · have hpl : ∀ c, ssPlace (kumZ p ζ θ) c = ζ ^ (c : ℕ) := by
        intro c; simp [ssPlace, kumZ, hτ0]
      intro x y hxy
      rw [hpl, hpl] at hxy
      have n1 := zeta_ne_one h3 ζ hζ
      have n2 := zeta_sq_ne_one h3 ζ hζ
      have n3 := zeta_ne_sq h3 ζ hζ
      have a01 : ζ ^ ((0 : Fin 3) : ℕ) ≠ ζ ^ ((1 : Fin 3) : ℕ) := by simpa using n1.symm
      have a02 : ζ ^ ((0 : Fin 3) : ℕ) ≠ ζ ^ ((2 : Fin 3) : ℕ) := by simpa using n2.symm
      have a12 : ζ ^ ((1 : Fin 3) : ℕ) ≠ ζ ^ ((2 : Fin 3) : ℕ) := by simpa using n3
      revert hxy
      fin_cases x <;> fin_cases y <;> intro hxy
      · rfl
      · exact absurd hxy a01
      · exact absurd hxy a02
      · exact absurd hxy.symm a01
      · rfl
      · exact absurd hxy a12
      · exact absurd hxy.symm a02
      · exact absurd hxy.symm a12
      · rfl
    · intro c
      simp only [kumZ, coeff_C_mul, hτ1]
      exact mul_ne_zero (pow_ne_zero _ (zeta_ne_zero ζ hζ)) (div_ne_zero hθ h3)
  exact ⟨hseq, fun LB hLB K hK => cer3 p hp5 _ hseq W hW LB hLB K hK⟩

/-- **`prop:cover3`** (covering windows in dimension three): let `p ≡ 1 (mod 3)` be prime, `ζ` a
primitive cube root of unity, `θ ≠ 0`, `u_d = θ/(3(1 - ζ^d))`, and let the windows satisfy (i)
`-u_d ∈ W_d` and (ii) every line `β + 𝔽_p (1, u_1, u_2)` meets `W_o × W_1 × W_2`. Then the choices exist
at every depth (for every history), a choice for all depths exists, and every resulting sequence is a
`(0,3)`-sequence with `c(P_{3K}) ≥ min(1, LB(W_o, W_1, W_2))` for every `K ≥ 1`. -/
theorem cover3 (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1) (ζ θ : ZMod p) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hθ : θ ≠ 0) (W : Fin 3 → Set (ZMod p)) (hi1 : -kumU ζ θ 1 ∈ W 1) (hi2 : -kumU ζ θ 2 ∈ W 2)
    (hcov : Covers3 (kumU ζ θ 1) (kumU ζ θ 2) W) :
    (∀ g : PowerSeries (ZMod p), constantCoeff g ≠ 0 → ∀ l, 1 ≤ l →
      ∃ g' : PowerSeries (ZMod p), (∀ j < l, coeff j g' = coeff j g) ∧
        (∀ K, l ≤ K → ∀ c : Fin 3, ∀ d, IsCarryEntry (kumGen p ζ θ g') K 0 l c c d → d ∈ W 0) ∧
        (∀ K, l + 1 ≤ K → ∀ c c' : Fin 3, ∀ d, c ≠ c' →
          IsCarryEntry (kumGen p ζ θ g') K 0 (l + 1) c c' d → d ∈ W (c - c'))) ∧
    (∃ g : PowerSeries (ZMod p), constantCoeff g = 1 ∧ RespIn3 (kumGen p ζ θ g) W) ∧
    (∀ g : PowerSeries (ZMod p), constantCoeff g ≠ 0 → RespIn3 (kumGen p ζ θ g) W →
      IsSeq0 (zcode p) (kumGen p ζ θ g) ∧
        ∀ LB : ℝ, C3bound p W LB → ∀ K, 1 ≤ K →
          SepAtLevel p 3 K (seqPoint (zcode p) (kumGen p ζ θ g)) (min 1 LB)) :=
  ⟨fun g hg l hl => cover3_step p hp3 ζ θ hζ hθ W hcov g hg l hl,
    cover3_exists p hp3 ζ θ hζ hθ W hi1 hi2 hcov,
    fun g hg hW => cover3_sep p hp3 ζ θ hζ hθ W g hg hW⟩

end Cover3

end GeoSeq
