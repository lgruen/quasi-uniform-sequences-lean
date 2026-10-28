/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Window
public import GeoSeq.WFLaw

@[expose] public section

/-!
# GeoSeq stage S7: steering (`prop:depthdir` for `s = 2`, `eq:steer`) and `thm:GA`

Faure frame (places `0, 1`), scaled local roots `z_0, z_1` (`z_0(0) = 0`, `[x]z_0 = -θ`, `z_1(0) = 1`).
By `lem:gform` the one-digit responses of column `c'` are, with `k = 1/((z_1 - z_0) g_{c'})`,
`a = g_{c'}(0)`, `a' = g_{1-c'}(0)`:
`O^{(l)} = [x^l] (1 - a z_1 k)/(1 - x)` (`ownR`) and `X^{(l)} = [x^l] a' z_0 k/(1 - x)` (`crossR`).

* `ownR_add`, `crossR_add` (**depth direction**, `prop:depthdir`, `s = 2`, in the free series `k`):
  changing `k` by `x^m e` leaves `O^{(n)}`, `n < m`, and `X^{(n)}`, `n ≤ m`, unchanged and moves
  `(O^{(m)}, X^{(m+1)})` by `-e(0)·(a, a'θ)`, a fixed direction (`eq:steer`: slope `1/κ`, `κ = a'θ/a`).
* `steer_step` (**the covering step**): condition (ii) gives, for EVERY `k` (any history), a value of the
  coefficient `m` that puts `(O^{(m)}, X^{(m+1)})` into the windows.
* `steer_exists` (**the rule never stops**): iterating the step (induction over the depth) gives one series
  `k` with all partial sums in the windows, `X^{(1)} = -κ` by condition (i).
* `ga_resp`: the responses of `ssGen g (faureZ p θ)` are `ownR`, `crossR` at every level (`prop:law` +
  `lem:gform`).
* **`GA_step`, `GA_exists`, `GA_sep`, `GA`** (`thm:GA`).
-/

namespace GeoSeq

open Finset PowerSeries

section Column

variable {F : Type*} [Field F]

/-- **Depth direction, own part**: `O^{(n)}` of `k + x^m e` is `O^{(n)}` of `k` for `n < m`, and
`O^{(m)}` moves by `-a e(0)` (`z_1(0) = 1`). -/
theorem ownR_add (z1 : PowerSeries F) (hz1 : constantCoeff z1 = 1) (a : F) (k e : PowerSeries F)
    (m n : ℕ) :
    ownR z1 a (k + X ^ m * e) n =
      ownR z1 a k n - (if m ≤ n then coeff (n - m) (C a * z1 * e * PowerSeries.mk 1) else 0) ∧
    ownR z1 a (k + X ^ m * e) m = ownR z1 a k m - a * constantCoeff e := by
  have key : ∀ n, ownR z1 a (k + X ^ m * e) n =
      ownR z1 a k n - (if m ≤ n then coeff (n - m) (C a * z1 * e * PowerSeries.mk 1) else 0) := by
    intro n
    unfold ownR
    rw [← coeff_X_pow_mul', ← map_sub]
    congr 1
    ring
  refine ⟨key n, ?_⟩
  rw [key m, if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  simp [hz1]

/-- **Depth direction, cross part**: `X^{(n)}` of `k + x^m e` is `X^{(n)}` of `k` for `n ≤ m`, and
`X^{(m+1)}` moves by `-a' θ e(0)` (`z_0(0) = 0`, `[x]z_0 = -θ`). -/
theorem crossR_add (z0 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0) (hz01 : coeff 1 z0 = -θ)
    (a : F) (k e : PowerSeries F) (m : ℕ) :
    (∀ n, n ≤ m → crossR z0 a (k + X ^ m * e) n = crossR z0 a k n) ∧
    crossR z0 a (k + X ^ m * e) (m + 1) = crossR z0 a k (m + 1) - a * θ * constantCoeff e := by
  obtain ⟨y, hy⟩ : X ∣ z0 := X_dvd_iff.mpr hz0
  have hy0 : constantCoeff y = -θ := by
    rw [← hz01, hy, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have key : ∀ n, crossR z0 a (k + X ^ m * e) n =
      crossR z0 a k n + coeff n (X ^ (m + 1) * (C a * y * e * PowerSeries.mk 1)) := by
    intro n
    unfold crossR
    rw [← map_add, hy]
    congr 1
    ring
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [key n, coeff_X_pow_mul', if_neg (by omega), add_zero]
  · rw [key, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    simp [hy0]
    ring

/-- `X^{(1)} = -a' θ k(0)`. -/
theorem crossR_one (z0 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0) (hz01 : coeff 1 z0 = -θ)
    (a : F) (k : PowerSeries F) : crossR z0 a k 1 = -(a * θ * constantCoeff k) := by
  obtain ⟨y, hy⟩ : X ∣ z0 := X_dvd_iff.mpr hz0
  have hy0 : constantCoeff y = -θ := by
    rw [← hz01, hy, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  unfold crossR
  rw [hy, show C a * (X * y) * k * PowerSeries.mk 1 = X * (C a * y * k * PowerSeries.mk 1) by ring,
    coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  simp [hy0]

/-- **The covering step** (condition (ii) of `thm:GA`): for every series `k` (every history) and every
depth `m`, some value `t` of the coefficient `m` puts `(O^{(m)}, X^{(m+1)})` into `Wo × Wx`. -/
theorem steer_step (z0 z1 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0)
    (hz01 : coeff 1 z0 = -θ) (hz1 : constantCoeff z1 = 1) (a a' : F) (ha : a ≠ 0)
    (Wo Wx : Set F) (hcov : ∀ β : F, ∃ o ∈ Wo, ∃ x ∈ Wx, (a' * θ / a) * (o - 1) - x = β)
    (k : PowerSeries F) (m : ℕ) :
    ∃ t : F, ownR z1 a (k + X ^ m * C t) m ∈ Wo ∧ crossR z0 a' (k + X ^ m * C t) (m + 1) ∈ Wx := by
  obtain ⟨o, ho, x, hx, hox⟩ :=
    hcov ((a' * θ / a) * (ownR z1 a k m - 1) - crossR z0 a' k (m + 1))
  refine ⟨(ownR z1 a k m - o) / a, ?_, ?_⟩
  · rw [(ownR_add z1 hz1 a k _ m m).2, constantCoeff_C]
    convert ho using 1
    field_simp
    ring
  · rw [(crossR_add z0 θ hz0 hz01 a' k _ m).2, constantCoeff_C]
    convert hx using 1
    field_simp at hox ⊢
    linear_combination hox

/-- The steered series, depth by depth: `approx 0 = k₀`, and `approx (m+1)` changes the coefficient
`m + 1` of `approx m` by a value chosen by `steer_step`. -/
noncomputable def steerApprox (choose : ℕ → PowerSeries F → F) (k₀ : PowerSeries F) :
    ℕ → PowerSeries F
  | 0 => k₀
  | m + 1 => steerApprox choose k₀ m + X ^ (m + 1) * C (choose (m + 1) (steerApprox choose k₀ m))

lemma steerApprox_coeff (choose : ℕ → PowerSeries F → F) (k₀ : PowerSeries F) (j n : ℕ)
    (hj : j ≤ n) : ∀ m, n ≤ m → coeff j (steerApprox choose k₀ m) = coeff j (steerApprox choose k₀ n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [steerApprox, map_add, coeff_X_pow_mul', if_neg (by omega), add_zero, ih]

/-- **The rule never stops** (`thm:GA`, existence by induction over the depth): there is a series `k`
with the prescribed constant term such that every own partial sum `O^{(l)}`, `l ≥ 1`, lies in `Wo` and every
cross partial sum `X^{(l)}`, `l ≥ 1`, lies in `Wx` (`X^{(1)} = -κ ∈ Wx` is condition (i)). -/
theorem steer_exists (z0 z1 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0)
    (hz01 : coeff 1 z0 = -θ) (hz1 : constantCoeff z1 = 1) (a a' : F) (ha : a ≠ 0)
    (Wo Wx : Set F) (hi : -(a' * θ / a) ∈ Wx)
    (hcov : ∀ β : F, ∃ o ∈ Wo, ∃ x ∈ Wx, (a' * θ / a) * (o - 1) - x = β) :
    ∃ k : PowerSeries F, constantCoeff k = a⁻¹ ∧
      ∀ l, 1 ≤ l → ownR z1 a k l ∈ Wo ∧ crossR z0 a' k l ∈ Wx := by
  classical
  let choose : ℕ → PowerSeries F → F := fun m k =>
    Classical.choose (steer_step z0 z1 θ hz0 hz01 hz1 a a' ha Wo Wx hcov k m)
  have hchoose : ∀ m k, ownR z1 a (k + X ^ m * C (choose m k)) m ∈ Wo ∧
      crossR z0 a' (k + X ^ m * C (choose m k)) (m + 1) ∈ Wx := fun m k =>
    Classical.choose_spec (steer_step z0 z1 θ hz0 hz01 hz1 a a' ha Wo Wx hcov k m)
  set ap := steerApprox choose (C a⁻¹)
  let k : PowerSeries F := PowerSeries.mk fun n => coeff n (ap n)
  -- `k` agrees with `ap n` up to the coefficient `n`
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
  refine ⟨k, hk0, fun l hl => ⟨?_, ?_⟩⟩
  · obtain ⟨e, he⟩ := hdvd l
    have h1 := (ownR_add z1 hz1 a (ap l) e (l + 1) l).1
    rw [if_neg (by omega), sub_zero, ← he] at h1
    rw [h1]
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact (hchoose (m + 1) (ap m)).1
  · rcases Nat.lt_or_ge l 2 with hl2 | hl2
    · obtain rfl : l = 1 := by omega
      convert hi using 1
      rw [crossR_one z0 θ hz0 hz01, hk0]
      field_simp
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 + 1 := ⟨l - 2, by omega⟩
      obtain ⟨e, he⟩ := hdvd (m + 1)
      have h1 := (crossR_add z0 θ hz0 hz01 a' (ap (m + 1)) e (m + 1 + 1)).1 (m + 1 + 1) le_rfl
      rw [← he] at h1
      rw [h1]
      exact (hchoose (m + 1) (ap m)).2

end Column

/-! ## The Faure frame with scale `θ` over `𝔽_p` -/

section FaureZ

lemma wfZ_facts {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (ρ : PowerSeries F)
    (hρ0 : constantCoeff ρ = 1) (θ : F) (hρ1 : coeff 1 ρ = 2 * θ) :
    constantCoeff (wfZ ρ 0) = 0 ∧ constantCoeff (wfZ ρ 1) = 1 ∧ coeff 1 (wfZ ρ 0) = -θ ∧
      coeff 1 (wfZ ρ 1) = θ ∧ wfZ ρ 0 + wfZ ρ 1 = 1 := by
  have hC : 2 * C (2 : F)⁻¹ = (1 : PowerSeries F) := by rw [← wf_two, wf_C2 h2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show constantCoeff (C (2 : F)⁻¹ * (1 - ρ)) = 0
    rw [map_mul, map_sub, map_one, hρ0, sub_self, mul_zero]
  · show constantCoeff (C (2 : F)⁻¹ * (1 + ρ)) = 1
    rw [map_mul, map_add, map_one, hρ0, constantCoeff_C, one_add_one_eq_two, inv_mul_cancel₀ h2]
  · show coeff 1 (C (2 : F)⁻¹ * (1 - ρ)) = -θ
    rw [coeff_C_mul, map_sub, coeff_one, if_neg one_ne_zero, hρ1]
    field_simp
    ring
  · show coeff 1 (C (2 : F)⁻¹ * (1 + ρ)) = θ
    rw [coeff_C_mul, map_add, coeff_one, if_neg one_ne_zero, hρ1]
    field_simp
    ring
  · show C (2 : F)⁻¹ * (1 - ρ) + C (2 : F)⁻¹ * (1 + ρ) = 1
    linear_combination hC

lemma cc_sub_one {F : Type*} [Field F] (a b : PowerSeries F) (ha : constantCoeff a = 1)
    (hb : constantCoeff b = 0) : constantCoeff (a - b) = 1 := by
  rw [map_sub, ha, hb, sub_zero]

lemma four_half {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (θ : F) : 4 * θ * (2 : F)⁻¹ = 2 * θ := by
  field_simp; ring

lemma quarter_four {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (θ : F) :
    (2 : F)⁻¹ * (2 : F)⁻¹ * (4 * θ) = θ := by
  field_simp; ring

/-- The scaled local roots `faureZ p θ`: `z_0(0) = 0`, `z_1(0) = 1`, `[x]z_0 = -θ`, `[x]z_1 = θ`,
`z_0 + z_1 = 1`. -/
theorem faureZ_facts (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (θ : ZMod p) :
    constantCoeff (faureZ p θ 0) = 0 ∧ constantCoeff (faureZ p θ 1) = 1 ∧
      coeff 1 (faureZ p θ 0) = -θ ∧ coeff 1 (faureZ p θ 1) = θ ∧
      faureZ p θ 0 + faureZ p θ 1 = 1 :=
  wfZ_facts (two_ne_zero_zmod p hp) (rhoWF p (4 * θ)) (rhoWF_const p _) θ
    ((rhoWF_coeff1 p _).trans (four_half (two_ne_zero_zmod p hp) θ))

/-- `eq:roots` for `faureZ p θ`: `z_c² - z_c = θ x`. -/
theorem faureZ_root (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (θ : ZMod p) (c : Fin 2) :
    Polynomial.aeval (faureZ p θ c) (Polynomial.X ^ 2 - Polynomial.X : Polynomial (ZMod p)) =
      C θ * X := by
  have h := wf_root (two_ne_zero_zmod p hp) (4 * θ) (rhoWF p (4 * θ)) (rhoWF_sq p hp _) c
  rw [quarter_four (two_ne_zero_zmod p hp)] at h
  exact h

/-- **The responses of a self-similar scramble of the Faure frame** (`prop:law` + `lem:gform`): with
`k_c = 1/((z_1 - z_0) g_c)`, column `c'` has the own response `ownR z_1 g_{c'}(0) k_{c'}` and the cross
response `crossR z_0 g_{1-c'}(0) k_{c'}`, at every level `K ≥ l ≥ 1`. -/
theorem ga_resp (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0)
    (g : Fin 2 → PowerSeries (ZMod p)) (hg : ∀ c, constantCoeff (g c) ≠ 0) (K l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) :
    IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 0 0 (ownR (faureZ p θ 1) (constantCoeff (g 0))
        ((faureZ p θ 1 - faureZ p θ 0) * g 0)⁻¹ l) ∧
      IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 1 0 (crossR (faureZ p θ 0) (constantCoeff (g 1))
        ((faureZ p θ 1 - faureZ p θ 0) * g 0)⁻¹ l) ∧
      IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 1 1 (ownR (faureZ p θ 1) (constantCoeff (g 1))
        ((faureZ p θ 1 - faureZ p θ 0) * g 1)⁻¹ l) ∧
      IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 0 1 (crossR (faureZ p θ 0) (constantCoeff (g 0))
        ((faureZ p θ 1 - faureZ p θ 0) * g 1)⁻¹ l) := by
  obtain ⟨hz0, hz1, -, -, hsum⟩ := faureZ_facts p (by omega) θ
  set z0 := faureZ p θ 0
  set z1 := faureZ p θ 1
  have hz : faureZ p θ = ![z0, z1] := by funext c; fin_cases c <;> rfl
  have hgv : g = ![g 0, g 1] := by funext c; fin_cases c <;> rfl
  have hρ : constantCoeff (z1 - z0) = 1 := cc_sub_one z1 z0 hz1 hz0
  have hk : ∀ c, ((z1 - z0) * g c)⁻¹ * ((z1 - z0) * g c) = 1 := fun c =>
    PowerSeries.inv_mul_cancel _ (by rw [map_mul, hρ, one_mul]; exact hg c)
  have hMG : frameM ![g 0, g 1] ![z0, z1] *
      faureG z0 z1 ((z1 - z0) * g 0)⁻¹ ((z1 - z0) * g 1)⁻¹ = 1 :=
    faure_inv z0 z1 (g 0) (g 1) _ _ (hk 0) (hk 1)
  have hdeg : (Polynomial.X ^ 2 - Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 2 :=
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hroot : ∀ c, Polynomial.aeval (![z0, z1] c)
      (Polynomial.X ^ 2 - Polynomial.X : Polynomial (ZMod p)) = C θ * X := by
    intro c; rw [← hz]; exact faureZ_root p (by omega) θ c
  have hlaw := fun c c' => law ![g 0, g 1] ![z0, z1] _ hdeg θ θ⁻¹ (mul_inv_cancel₀ hθ) hroot _ hMG
    K 0 l hl hlK c c'
  have hgf := gform z0 z1 (g 0) (g 1) ((z1 - z0) * g 0)⁻¹ ((z1 - z0) * g 1)⁻¹ hz0 hsum l
  rw [hz, hgv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hlaw 0 0; rwa [hgf.1] at this
  · have := hlaw 1 0; rwa [hgf.2.2.1] at this
  · have := hlaw 1 1; rwa [hgf.2.2.2] at this
  · have := hlaw 0 1; rwa [hgf.2.1] at this

end FaureZ

/-! ## `thm:GA` -/

section GA

lemma ps_inv_inv {F : Type*} [Field F] (u k : PowerSeries F) (hu : constantCoeff u = 1)
    (hk : constantCoeff k ≠ 0) : (u * (u * k)⁻¹)⁻¹ = k := by
  have huk : constantCoeff (u * k) ≠ 0 := by rw [map_mul, hu, one_mul]; exact hk
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [map_mul, hu, one_mul, constantCoeff_inv]; exact inv_ne_zero huk)]
  calc k * (u * (u * k)⁻¹) = (u * k) * (u * k)⁻¹ := by ring
    _ = 1 := PowerSeries.mul_inv_cancel _ huk

lemma ps_cc_inv {F : Type*} [Field F] (u k : PowerSeries F) (hu : constantCoeff u = 1) :
    constantCoeff (u * k)⁻¹ = (constantCoeff k)⁻¹ := by
  rw [constantCoeff_inv, map_mul, hu, one_mul]

lemma ps_inv_add {F : Type*} [Field F] (u k e : PowerSeries F) (l : ℕ) (hl : 1 ≤ l)
    (hu : constantCoeff u = 1) (hk : constantCoeff k ≠ 0) :
    ∃ f, (u * (k + X ^ l * e))⁻¹ = (u * k)⁻¹ + X ^ l * f := by
  have hk' : constantCoeff (k + X ^ l * e) = constantCoeff k := by
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    simp [pow_succ]
  have hA : (u * (k + X ^ l * e)) * (u * (k + X ^ l * e))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [map_mul, hu, one_mul, hk']; exact hk)
  have hB : (u * k) * (u * k)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [map_mul, hu, one_mul]; exact hk)
  refine ⟨-((u * (k + X ^ l * e))⁻¹ * (u * k)⁻¹ * u * e), ?_⟩
  linear_combination (u * k)⁻¹ * hA - (u * (k + X ^ l * e))⁻¹ * hB

lemma kappa_facts {F : Type*} [Field F] (θ κ01 κ10 a0 a1 : F) (hθ : θ ≠ 0) (h01 : κ01 ≠ 0)
    (hκ : κ01 * κ10 = θ ^ 2) (ha1 : a1 ≠ 0) (hr : κ01 * a1 = θ * a0) :
    a0 ≠ 0 ∧ a0 * θ / a1 = κ01 ∧ a1 * θ / a0 = κ10 := by
  have ha0 : a0 ≠ 0 := by
    intro h; rw [h, mul_zero] at hr; exact mul_ne_zero h01 ha1 hr
  refine ⟨ha0, ?_, ?_⟩
  · field_simp; linear_combination -hr
  · field_simp
    have : κ01 * (a1 * θ) = κ01 * (a0 * κ10) := by linear_combination θ * hr - a0 * hκ
    exact mul_left_cancel₀ h01 this

/-- **`thm:GA`, the choices exist at every depth for every history**: for every pair of multipliers `g`
(normalised by `κ_{0←1} g_1(0) = θ g_0(0)`) and every depth `l ≥ 1` there are multipliers `g'` that agree
with `g` in the coefficients `< l` and put the depth-`l` responses of both columns into the windows:
`O_{c'}^{(l)} ∈ W_o^{(c')}`, `X_{1-c'←c'}^{(l+1)} ∈ W_x^{(c')}` (at every level where they are defined). -/
theorem GA_step (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 κ10 : ZMod p) (hθ : θ ≠ 0)
    (h01 : κ01 ≠ 0) (hκ : κ01 * κ10 = θ ^ 2) (Wo Wx : Fin 2 → Set (ZMod p))
    (hc0 : Covers κ10 (Wo 0) (Wx 0)) (hc1 : Covers κ01 (Wo 1) (Wx 1))
    (g : Fin 2 → PowerSeries (ZMod p)) (hg1 : constantCoeff (g 1) ≠ 0)
    (hgr : κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0)) (l : ℕ) (hl : 1 ≤ l) :
    ∃ g' : Fin 2 → PowerSeries (ZMod p), (∀ c, ∀ j < l, coeff j (g' c) = coeff j (g c)) ∧
      (∀ K d, l ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 0 0 d → d ∈ Wo 0) ∧
        (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 1 1 d → d ∈ Wo 1)) ∧
      (∀ K d, l + 1 ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 1 0 d → d ∈ Wx 0) ∧
        (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 0 1 d → d ∈ Wx 1)) := by
  obtain ⟨hz0, hz1, hz01, -, -⟩ := faureZ_facts p (by omega) θ
  set z0 := faureZ p θ 0
  set z1 := faureZ p θ 1
  obtain ⟨hg0, hκ1, hκ0⟩ := kappa_facts θ κ01 κ10 _ _ hθ h01 hκ hg1 hgr
  have hρ : constantCoeff (z1 - z0) = 1 := cc_sub_one z1 z0 hz1 hz0
  have hg : ∀ c, constantCoeff (g c) ≠ 0 := by intro c; fin_cases c; exacts [hg0, hg1]
  set k : Fin 2 → PowerSeries (ZMod p) := fun c => ((z1 - z0) * g c)⁻¹ with hkdef
  have hkc : ∀ c, constantCoeff (k c) = (constantCoeff (g c))⁻¹ := fun c =>
    ps_cc_inv _ _ hρ
  have hkne : ∀ c, constantCoeff (k c) ≠ 0 := fun c => by rw [hkc]; exact inv_ne_zero (hg c)
  obtain ⟨t0, ht0o, ht0x⟩ := steer_step z0 z1 θ hz0 hz01 hz1 _ _ hg0 (Wo 0) (Wx 0)
    (by rw [hκ0]; exact hc0) (k 0) l
  obtain ⟨t1, ht1o, ht1x⟩ := steer_step z0 z1 θ hz0 hz01 hz1 _ _ hg1 (Wo 1) (Wx 1)
    (by rw [hκ1]; exact hc1) (k 1) l
  set k' : Fin 2 → PowerSeries (ZMod p) := ![k 0 + X ^ l * C t0, k 1 + X ^ l * C t1] with hk'def
  have hk'c : ∀ c, ∃ t, k' c = k c + X ^ l * C t := by
    intro c; fin_cases c; exacts [⟨t0, rfl⟩, ⟨t1, rfl⟩]
  set g' : Fin 2 → PowerSeries (ZMod p) := fun c => ((z1 - z0) * k' c)⁻¹ with hg'def
  have hgk : ∀ c, g c = ((z1 - z0) * k c)⁻¹ := fun c => (ps_inv_inv _ _ hρ (hg c)).symm
  have hagree : ∀ c, ∃ f, g' c = g c + X ^ l * f := by
    intro c
    obtain ⟨t, ht⟩ := hk'c c
    rw [hg'def, hgk c]
    simp only [ht]
    exact ps_inv_add _ _ _ l hl hρ (hkne c)
  have hcoef : ∀ c, ∀ j < l, coeff j (g' c) = coeff j (g c) := by
    intro c j hj
    obtain ⟨f, hf⟩ := hagree c
    rw [hf, map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]
  have hcc : ∀ c, constantCoeff (g' c) = constantCoeff (g c) := fun c => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, hcoef c 0 hl]
  have hg' : ∀ c, constantCoeff (g' c) ≠ 0 := fun c => by rw [hcc]; exact hg c
  have hk'ne : ∀ c, constantCoeff (k' c) ≠ 0 := by
    intro c
    obtain ⟨t, ht⟩ := hk'c c
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [ht]; simpa [pow_succ] using hkne c
  have hgk' : ∀ c, ((z1 - z0) * g' c)⁻¹ = k' c := fun c => ps_inv_inv _ _ hρ (hk'ne c)
  refine ⟨g', hcoef, fun K d hK => ?_, fun K d hK => ?_⟩
  · obtain ⟨r00, -, r11, -⟩ := ga_resp p hp θ hθ g' hg' K l hl hK
    rw [hgk' 0, hcc 0] at r00
    rw [hgk' 1, hcc 1] at r11
    exact ⟨fun h => carryEntry_unique _ _ _ _ _ _ h r00 ▸ ht0o,
      fun h => carryEntry_unique _ _ _ _ _ _ h r11 ▸ ht1o⟩
  · obtain ⟨-, r10, -, r01⟩ := ga_resp p hp θ hθ g' hg' K (l + 1) (by omega) hK
    rw [hgk' 0, hcc 1] at r10
    rw [hgk' 1, hcc 0] at r01
    exact ⟨fun h => carryEntry_unique _ _ _ _ _ _ h r10 ▸ ht0x,
      fun h => carryEntry_unique _ _ _ _ _ _ h r01 ▸ ht1x⟩

/-- **`thm:GA`, existence**: under conditions (i), (ii) there are multipliers `g` (normalised by
`κ_{0←1} g_1(0) = θ g_0(0)`, i.e. `λ_0/λ_1 = κ_{0←1}/θ`) all of whose responses lie in the windows at
every level. -/
theorem GA_exists (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 κ10 : ZMod p) (hθ : θ ≠ 0)
    (h01 : κ01 ≠ 0) (hκ : κ01 * κ10 = θ ^ 2) (Wo Wx : Fin 2 → Set (ZMod p))
    (hi0 : -κ10 ∈ Wx 0) (hi1 : -κ01 ∈ Wx 1)
    (hc0 : Covers κ10 (Wo 0) (Wx 0)) (hc1 : Covers κ01 (Wo 1) (Wx 1)) :
    ∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p θ)) Wo Wx := by
  obtain ⟨hz0, hz1, hz01, -, -⟩ := faureZ_facts p (by omega) θ
  set z0 := faureZ p θ 0
  set z1 := faureZ p θ 1
  have hρ : constantCoeff (z1 - z0) = 1 := cc_sub_one z1 z0 hz1 hz0
  set a0 : ZMod p := κ01 / θ with ha0def
  have hr : κ01 * 1 = θ * a0 := by rw [ha0def]; field_simp
  obtain ⟨ha0, hκ1, hκ0⟩ := kappa_facts θ κ01 κ10 a0 1 hθ h01 hκ one_ne_zero hr
  obtain ⟨k1, hk1c, hk1W⟩ := steer_exists z0 z1 θ hz0 hz01 hz1 1 a0 one_ne_zero (Wo 1) (Wx 1)
    (by rw [hκ1]; exact hi1) (by rw [hκ1]; exact hc1)
  obtain ⟨k0, hk0c, hk0W⟩ := steer_exists z0 z1 θ hz0 hz01 hz1 a0 1 ha0 (Wo 0) (Wx 0)
    (by rw [hκ0]; exact hi0) (by rw [hκ0]; exact hc0)
  set g : Fin 2 → PowerSeries (ZMod p) := ![((z1 - z0) * k0)⁻¹, ((z1 - z0) * k1)⁻¹] with hgdef
  have hg0c : constantCoeff (g 0) = a0 := by
    show constantCoeff ((z1 - z0) * k0)⁻¹ = a0
    rw [ps_cc_inv _ _ hρ, hk0c, inv_inv]
  have hg1c : constantCoeff (g 1) = 1 := by
    show constantCoeff ((z1 - z0) * k1)⁻¹ = 1
    rw [ps_cc_inv _ _ hρ, hk1c, inv_one, inv_one]
  have hgk0 : ((z1 - z0) * g 0)⁻¹ = k0 :=
    ps_inv_inv _ _ hρ (by rw [hk0c]; exact inv_ne_zero ha0)
  have hgk1 : ((z1 - z0) * g 1)⁻¹ = k1 :=
    ps_inv_inv _ _ hρ (by rw [hk1c]; exact inv_ne_zero one_ne_zero)
  have hg : ∀ c, constantCoeff (g c) ≠ 0 := by
    intro c; fin_cases c
    · show constantCoeff (g 0) ≠ 0; rw [hg0c]; exact ha0
    · show constantCoeff (g 1) ≠ 0; rw [hg1c]; exact one_ne_zero
  refine ⟨g, by rw [hg1c]; exact one_ne_zero, by rw [hg1c, hg0c]; exact hr, ?_⟩
  intro K l hl hlK d
  obtain ⟨r00, r10, r11, r01⟩ := ga_resp p hp θ hθ g hg K l hl hlK
  rw [hgk0, hg0c] at r00
  rw [hgk0, hg1c] at r10
  rw [hgk1, hg1c] at r11
  rw [hgk1, hg0c] at r01
  exact ⟨fun h => carryEntry_unique _ _ _ _ _ _ h r00 ▸ (hk0W l hl).1,
    fun h => carryEntry_unique _ _ _ _ _ _ h r10 ▸ (hk0W l hl).2,
    fun h => carryEntry_unique _ _ _ _ _ _ h r11 ▸ (hk1W l hl).1,
    fun h => carryEntry_unique _ _ _ _ _ _ h r01 ▸ (hk1W l hl).2⟩

/-- **`thm:GA`, every choice**: a self-similar scramble of the Faure frame with scale `θ` and multipliers
`g` (`g_1(0) ≠ 0`, `κ_{0←1} g_1(0) = θ g_0(0)`) whose responses lie in the windows is a `(0,2)`-sequence,
and `c(P_{2K}) ≥ min(1, LB)` for every `K ≥ 1` and every `LB` below the four numbers of `thm:GA`. -/
theorem GA_sep (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 : ZMod p) (hθ : θ ≠ 0) (h01 : κ01 ≠ 0)
    (Wo Wx : Fin 2 → Set (ZMod p)) (g : Fin 2 → PowerSeries (ZMod p))
    (hg1 : constantCoeff (g 1) ≠ 0) (hgr : κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0))
    (hW : RespIn (ssGen g (faureZ p θ)) Wo Wx) :
    IsSeq0 (zcode p) (ssGen g (faureZ p θ)) ∧
      ∀ LB : ℝ, GAbound p Wo Wx LB → ∀ K, 1 ≤ K →
        SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p θ))) (min 1 LB) := by
  obtain ⟨hz0, hz1, hz01, hz11, -⟩ := faureZ_facts p (by omega) θ
  have hg0 : constantCoeff (g 0) ≠ 0 := by
    intro h; rw [h, mul_zero] at hgr; exact mul_ne_zero h01 hg1 hgr
  have hseq : IsSeq0 (zcode p) (ssGen g (faureZ p θ)) := by
    refine ss_t0 (zcode p) _ _ ?_ ?_ ?_
    · intro x y hxy
      have h01' : ssPlace (faureZ p θ) 0 ≠ ssPlace (faureZ p θ) 1 := by
        show constantCoeff (faureZ p θ 0) ≠ constantCoeff (faureZ p θ 1)
        rw [hz0, hz1]; exact zero_ne_one
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd hxy h01'
      · exact absurd hxy.symm h01'
      · rfl
    · intro c; fin_cases c; exacts [hg0, hg1]
    · intro c; fin_cases c
      · show coeff 1 (faureZ p θ 0) ≠ 0; rw [hz01]; exact neg_ne_zero.mpr hθ
      · show coeff 1 (faureZ p θ 1) ≠ 0; rw [hz11]; exact hθ
  exact ⟨hseq, fun LB hLB K hK => win_cert p hp _ hseq Wo Wx hW LB hLB K hK⟩

/-- **`thm:GA`** (covering windows): let `p ≥ 5` be prime, `θ, κ_{0←1}, κ_{1←0} ∈ 𝔽_p^*` with
`κ_{0←1} κ_{1←0} = θ²`, and windows with (i) `-κ_{1-c'←c'} ∈ W_x^{(c')}` and (ii)
`κ_{1-c'←c'}(W_o^{(c')} - 1) - W_x^{(c')} = 𝔽_p`. Then (1) the choices exist at every depth, for every
history (`GA_step`); (2) a choice for all depths exists (`GA_exists`); (3) every resulting sequence is a
`(0,2)`-sequence with `c(P_{2K}) ≥ min(1, LB^GA)` for every `K ≥ 1` (`GA_sep`). The scramble is
parametrised by its multipliers `g_c` (equivalently `(λ_c, ψ_c)`, `prop:LI`(a)), normalised by
`κ_{0←1} g_1(0) = θ g_0(0)`. -/
theorem GA (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 κ10 : ZMod p) (hθ : θ ≠ 0)
    (h01 : κ01 ≠ 0) (hκ : κ01 * κ10 = θ ^ 2) (Wo Wx : Fin 2 → Set (ZMod p))
    (hi0 : -κ10 ∈ Wx 0) (hi1 : -κ01 ∈ Wx 1)
    (hc0 : Covers κ10 (Wo 0) (Wx 0)) (hc1 : Covers κ01 (Wo 1) (Wx 1)) :
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) → ∀ l, 1 ≤ l →
      ∃ g' : Fin 2 → PowerSeries (ZMod p), (∀ c, ∀ j < l, coeff j (g' c) = coeff j (g c)) ∧
        (∀ K d, l ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 0 0 d → d ∈ Wo 0) ∧
          (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 1 1 d → d ∈ Wo 1)) ∧
        (∀ K d, l + 1 ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 1 0 d → d ∈ Wx 0) ∧
          (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 0 1 d → d ∈ Wx 1))) ∧
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p θ)) Wo Wx) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p θ)) Wo Wx →
      IsSeq0 (zcode p) (ssGen g (faureZ p θ)) ∧
        ∀ LB : ℝ, GAbound p Wo Wx LB → ∀ K, 1 ≤ K →
          SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p θ))) (min 1 LB)) :=
  ⟨fun g hg1 hgr l hl => GA_step p hp θ κ01 κ10 hθ h01 hκ Wo Wx hc0 hc1 g hg1 hgr l hl,
    GA_exists p hp θ κ01 κ10 hθ h01 hκ Wo Wx hi0 hi1 hc0 hc1,
    fun g hg1 hgr hW => GA_sep p hp θ κ01 hθ h01 Wo Wx g hg1 hgr hW⟩

end GA

end GeoSeq
