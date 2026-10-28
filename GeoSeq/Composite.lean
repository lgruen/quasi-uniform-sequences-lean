/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S10: `prop:composite` (composite dimension)

Directions of the twisted symmetric Kummer family: `u_d = twU s θ ϱ ζ d = θ ϱ^d / (s (1 - ζ^d))`.

* **`composite_a`** (`prop:composite`(a)): `ϱ = 1`: `u_d + u_{s-d} = θ/s`; `composite_a4`: `u_1 - 2u_2 + u_3 = 0`
  for `s = 4`.
* **`composite_c`** (`prop:composite`(c)): an integer relation `∑ ξ_d u_d = 0`, `ξ ≢ 0 (mod p)`, and a
  product window `W_o × ∏_d W_d` with `W_d ⊆ [-b_d, b_d]` meeting every line of direction `(1, u)` force
  `2 ∑_d |ξ_d| b_d ≥ p - 1`.
* **`composite_s4`**: the "in particular" for `s = 4`, `ϱ = 1`: `b_1 + 2b_2 + b_3 ≥ (p-1)/2` and
  `∑ b_d ≥ (p-1)/4`.
* `composite_b` (`prop:composite`(b), cyclotomic integer relation) — see `GeoSeq/CompositeB.lean`.
-/

namespace GeoSeq

open Finset

/-- **`prop:composite`(a)**: for the untwisted family (`ϱ = 1`), `u_d + u_{s-d} = θ/s` whenever `ζ^s = 1`,
`ζ^d ≠ 1`, `d ≤ s`. -/
theorem composite_a {F : Type*} [Field F] (s : ℕ) (θ ζ : F) (hs : (s : F) ≠ 0) (hζ : ζ ^ s = 1)
    (d : ℕ) (hd : d ≤ s) (hζd : ζ ^ d ≠ 1) :
    twU s θ 1 ζ d + twU s θ 1 ζ (s - d) = θ / s := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hs
    · simp [zero_pow h.ne'] at hζ
  have hsd : ζ ^ (s - d) * ζ ^ d = 1 := by rw [← pow_add, Nat.sub_add_cancel hd, hζ]
  have h1 : (1 : F) - ζ ^ d ≠ 0 := sub_ne_zero.2 (Ne.symm hζd)
  have h2 : (1 : F) - ζ ^ (s - d) ≠ 0 := by
    intro h
    have : ζ ^ (s - d) = 1 := (sub_eq_zero.1 h).symm
    rw [this, one_mul] at hsd
    exact hζd hsd
  unfold twU
  simp only [one_pow, mul_one]
  rw [div_add_div _ _ (mul_ne_zero hs h1) (mul_ne_zero hs h2), div_eq_div_iff
    (mul_ne_zero (mul_ne_zero hs h1) (mul_ne_zero hs h2)) hs]
  linear_combination (-(θ * s * s)) * hsd

/-- `prop:composite`(a) for `s = 4`: `u_1 - 2u_2 + u_3 = 0` (`ζ` a primitive fourth root of unity,
characteristic `≠ 2`). -/
theorem composite_a4 {F : Type*} [Field F] (θ ζ : F) (h2 : (2 : F) ≠ 0) (hζ : ζ ^ 2 = -1) :
    twU 4 θ 1 ζ 1 - 2 * twU 4 θ 1 ζ 2 + twU 4 θ 1 ζ 3 = 0 := by
  have h4 : ((4 : ℕ) : F) ≠ 0 := by
    have : ((4 : ℕ) : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hζ4 : ζ ^ 4 = 1 := by
    have : ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
    rw [this, hζ]; ring
  have hζ1 : ζ ^ 1 ≠ 1 := by
    intro h; rw [pow_one] at h; rw [h] at hζ; norm_num at hζ
    exact h2 (by linear_combination hζ)
  have ha := composite_a 4 θ ζ h4 hζ4 1 (by norm_num) hζ1
  have hu2 : twU 4 θ 1 ζ 2 = θ / 8 := by
    unfold twU; rw [hζ, one_pow, mul_one]
    have : ((4 : ℕ) : F) * (1 - -1) = 8 := by norm_num
    rw [this]
  have : twU 4 θ 1 ζ (4 - 1) = twU 4 θ 1 ζ 3 := rfl
  rw [this] at ha
  rw [hu2]
  have e : ((4 : ℕ) : F) = 4 := by norm_num
  rw [e] at ha
  have h4' : (4 : F) ≠ 0 := by rw [← e]; exact h4
  have h8 : (2 : F) * (θ / 8) = θ / 4 := by
    have : (8 : F) = 2 * 4 := by norm_num
    rw [this]; field_simp
  rw [h8]
  linear_combination ha

/-- **`prop:composite`(c)**: let `ξ ∈ ℤ^{s-1}` with `ξ ≢ 0 (mod p)` and `∑_d ξ_d u_d = 0` in `𝔽_p`, and let
`W = W_o × ∏_d W_d ⊆ 𝔽_p^s` with every element of `W_d` represented by an integer in `[-b_d, b_d]`. If
every line `β + 𝔽_p (1, u)` meets `W`, then `2 ∑_d |ξ_d| b_d ≥ p - 1`. -/
theorem composite_c (p : ℕ) [Fact p.Prime] (m : ℕ) (ξ : Fin m → ℤ) (hξ : ∃ d, (ξ d : ZMod p) ≠ 0)
    (u : Fin m → ZMod p) (hrel : ∑ d, (ξ d : ZMod p) * u d = 0)
    (Wo : Set (ZMod p)) (Wd : Fin m → Set (ZMod p)) (b : Fin m → ℕ)
    (hWd : ∀ d, ∀ x ∈ Wd d, ∃ k : ℤ, |k| ≤ b d ∧ (k : ZMod p) = x)
    (hline : ∀ (βo : ZMod p) (β : Fin m → ZMod p), ∃ t : ZMod p,
      βo + t ∈ Wo ∧ ∀ d, β d + t * u d ∈ Wd d) :
    p ≤ 2 * ∑ d, (ξ d).natAbs * b d + 1 := by
  obtain ⟨d0, hd0⟩ := hξ
  set B : ℤ := ∑ d, |ξ d| * (b d : ℤ) with hB
  -- every residue is `∑ ξ_d k_d` with `|k_d| ≤ b_d`
  have hcov : ∀ y : ZMod p, ∃ z ∈ Finset.Icc (-B) B, (z : ZMod p) = y := by
    intro y
    obtain ⟨t, -, ht⟩ := hline 0 (Pi.single d0 (y * (ξ d0 : ZMod p)⁻¹))
    choose k hk hkx using fun d => hWd d _ (ht d)
    refine ⟨∑ d, ξ d * k d, ?_, ?_⟩
    · have habs : |∑ d, ξ d * k d| ≤ B := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hk d) (abs_nonneg _)
      exact Finset.mem_Icc.2 (abs_le.1 habs)
    · push_cast
      simp_rw [hkx]
      simp only [mul_add, Finset.sum_add_distrib]
      have e2 : ∑ d, (ξ d : ZMod p) * (t * u d) = t * ∑ d, (ξ d : ZMod p) * u d := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_; ring
      rw [e2, hrel, mul_zero, add_zero, Finset.sum_eq_single d0]
      · rw [Pi.single_eq_same]; field_simp
      · intro d _ hd; rw [Pi.single_eq_of_ne hd, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ (Finset.Icc (-B) B).image (fun z : ℤ => (z : ZMod p)) := by
    intro y _
    obtain ⟨z, hz, rfl⟩ := hcov y
    exact Finset.mem_image_of_mem _ hz
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_univ, ZMod.card, Int.card_Icc] at hc
  have hBn : B = ((∑ d, (ξ d).natAbs * b d : ℕ) : ℤ) := by
    rw [hB]; push_cast; rfl
  rw [hBn] at hc
  omega

/-- **`prop:composite`, "in particular"** (`s = 4`, `ϱ = 1`, `p ≡ 1 (mod 4)`): every product window meeting
all lines of direction `α = (1, u_1, u_2, u_3)` has `b_1 + 2b_2 + b_3 ≥ (p-1)/2`, so its cross windows
have total half-width `≥ (p-1)/4`. -/
theorem composite_s4 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (θ ζ : ZMod p) (hζ : ζ ^ 2 = -1)
    (Wo : Set (ZMod p)) (Wd : Fin 3 → Set (ZMod p)) (b : Fin 3 → ℕ)
    (hWd : ∀ d, ∀ x ∈ Wd d, ∃ k : ℤ, |k| ≤ b d ∧ (k : ZMod p) = x)
    (hline : ∀ (βo : ZMod p) (β : Fin 3 → ZMod p), ∃ t : ZMod p,
      βo + t ∈ Wo ∧ ∀ d, β d + t * twU 4 θ 1 ζ (d + 1) ∈ Wd d) :
    p - 1 ≤ 2 * (b 0 + 2 * b 1 + b 2) ∧ p - 1 ≤ 4 * (b 0 + b 1 + b 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hrel := composite_a4 θ ζ h2 hζ
  have hc := composite_c p 3 ![1, -2, 1] ⟨0, by simp⟩ (fun d => twU 4 θ 1 ζ (d + 1))
    (by simp [Fin.sum_univ_three]; linear_combination hrel) Wo Wd b hWd hline
  simp [Fin.sum_univ_three] at hc
  omega

end GeoSeq
