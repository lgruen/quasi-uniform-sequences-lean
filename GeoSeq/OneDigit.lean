/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# GeoSeq stage S0 proofs: the one-digit certificate (`rem:onedigit`) and the arithmetic core of
`thm:WF`

* `gapNum1_zero`, `gapNum1_eq`: closed form of `f_1(e, σ)` over `ℤ/qℤ` (the difference
  `val(r + σ) - val(r)` takes exactly the values `val σ` and `val σ - q` for `σ ≠ 0`).
* `rem:onedigit`: `F1_one_neg` (`f_1(1, -A) = 1 - (A+1)/q`), `F1_one_one` (`f_1(1, 1) = 0`),
  `F1_neg` (`f_1(-1, σ) = f_1(1, -σ)`), and `F1_zero_half` (`f_1(0, ±1/2) = (p-3)/(2p)`).
* `WF_coord1`: the coordinate-1 part of the proof of `thm:WF`, for every prime `p ≥ 5`: with the
  frozen responses `O_1^{(l)} = 0`, `X_{1←0}^{(l)} = ±1/2` of `lem:WFlaw`, every step
  `e ∈ {-1,0,1}² ∖ {0}` has `f_1(e_1, σ_1) ≥ (p-3)/(2p)`; `WF_LB1` adds the coordinate-0 term.
* `gapNum_one`: the general `gapNum` at depth `j = 1` is `gapNum1`.
* `WF_coord1_p7`: the same finite statement at `p = 7` by kernel `decide` (independent check).
-/

namespace GeoSeq

open Finset

/-- The difference `val(r + σ) - val(r)` is `val σ` or `val σ - q`. -/
theorem val_add_sub (q : ℕ) [NeZero q] (r σ : ZMod q) :
    ((r + σ).val : ℤ) - r.val = σ.val ∨ ((r + σ).val : ℤ) - r.val = (σ.val : ℤ) - q := by
  have h := ZMod.val_add r σ
  have hr := ZMod.val_lt r
  have hs := ZMod.val_lt σ
  rcases lt_or_ge (r.val + σ.val) q with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    left; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at h
    right; omega

/-- `f_1(e, 0)`: numerator `|e q| - 1`. -/
theorem gapNum1_zero (q : ℕ) [NeZero q] (e : ℤ) : gapNum1 q e 0 = (e * q).natAbs - 1 := by
  unfold gapNum1
  congr 1
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simp)
  · apply Finset.le_min'
    intro y hy
    simp only [mem_image, mem_univ, true_and, add_zero] at hy
    obtain ⟨r, rfl⟩ := hy
    simp

/-- **Closed form of `f_1` over `ℤ/qℤ`** (`rem:onedigit`): for `σ ≠ 0`, numerator
`min(|e q + val σ|, |e q + val σ - q|) - 1`. -/
theorem gapNum1_eq (q : ℕ) [NeZero q] (e : ℤ) (σ : ZMod q) (hσ : σ ≠ 0) :
    gapNum1 q e σ =
      min (e * q + σ.val).natAbs (e * q + σ.val - q).natAbs - 1 := by
  unfold gapNum1
  congr 1
  apply le_antisymm
  · rcases le_total (e * q + σ.val).natAbs (e * q + σ.val - q).natAbs with h | h
    · rw [min_eq_left h]
      apply Finset.min'_le
      simp only [mem_image, mem_univ, true_and]
      exact ⟨0, by simp⟩
    · rw [min_eq_right h]
      apply Finset.min'_le
      simp only [mem_image, mem_univ, true_and]
      refine ⟨-σ, ?_⟩
      have hv : ((-σ : ZMod q).val : ℤ) = q - σ.val := by
        rw [ZMod.neg_val]
        simp only [hσ, ↓reduceIte]
        have := ZMod.val_lt σ
        push_cast [this.le]
        ring
      rw [neg_add_cancel, ZMod.val_zero, hv]
      congr 1
      ring
  · apply Finset.le_min'
    intro y hy
    simp only [mem_image, mem_univ, true_and] at hy
    obtain ⟨r, rfl⟩ := hy
    rcases val_add_sub q r σ with h | h
    · have : e * q + ((r + σ).val : ℤ) - r.val = e * q + σ.val := by linarith
      rw [this]; exact min_le_left _ _
    · have : e * q + ((r + σ).val : ℤ) - r.val = e * q + σ.val - q := by linarith
      rw [this]; exact min_le_right _ _

/-- **`rem:onedigit`**: `f_1(1, -A) = 1 - (A+1)/q` for `0 ≤ A < q` (numerators). -/
theorem F1_one_neg (q : ℕ) [NeZero q] (A : ℕ) (hA : A < q) :
    gapNum1 q 1 (-(A : ZMod q)) = q - 1 - A := by
  rcases Nat.eq_zero_or_pos A with rfl | hA0
  · simp [gapNum1_zero]
  · have hne : (A : ZMod q) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hA0 h) (by omega)
    have hn : -(A : ZMod q) ≠ 0 := neg_ne_zero.mpr hne
    rw [gapNum1_eq q 1 _ hn, ZMod.neg_val]
    simp only [hne, ↓reduceIte, ZMod.val_natCast, Nat.mod_eq_of_lt hA]
    omega

/-- **`rem:onedigit`**: the fatal forward shift, `f_1(1, 1) = 0` (`q ≥ 2`). -/
theorem F1_one_one (q : ℕ) [NeZero q] (hq : 2 ≤ q) : gapNum1 q 1 1 = 0 := by
  have : Fact (1 < q) := ⟨hq⟩
  rw [gapNum1_eq q 1 1 one_ne_zero, ZMod.val_one]
  omega

/-- **`rem:onedigit`**: `f_1(-1, σ) = f_1(1, -σ)`. -/
theorem F1_neg (q : ℕ) [NeZero q] (σ : ZMod q) : gapNum1 q (-1) σ = gapNum1 q 1 (-σ) := by
  by_cases hσ : σ = 0
  · subst hσ; simp [gapNum1_zero]
  · have hn : -σ ≠ 0 := neg_ne_zero.mpr hσ
    rw [gapNum1_eq q (-1) σ hσ, gapNum1_eq q 1 (-σ) hn, ZMod.neg_val]
    simp only [hσ, ↓reduceIte]
    have := ZMod.val_lt σ
    rw [min_comm]
    omega

/-- In `ℤ/pℤ`, `p` an odd prime, `1/2` is the residue `(p+1)/2`. -/
theorem half_val (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    2 * ((2 : ZMod p)⁻¹).val = p + 1 := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hmul : (((p + 1) / 2 : ℕ) : ZMod p) * 2 = 1 := by
    have : ((p + 1) / 2) * 2 = p + 1 := by omega
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ← Nat.cast_mul, this]
    simp
  have hinv : (2 : ZMod p)⁻¹ = (((p + 1) / 2 : ℕ) : ZMod p) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  rw [hinv, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The two residues `±1/2` are nonzero, with `2 val = p ± 1`. -/
theorem half_cases (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (σ : ZMod p)
    (hσ : σ = (2 : ZMod p)⁻¹ ∨ σ = -(2 : ZMod p)⁻¹) :
    σ ≠ 0 ∧ (2 * σ.val = p + 1 ∨ 2 * σ.val = p - 1) := by
  have h2 := half_val p hp
  have hlt := ZMod.val_lt (2 : ZMod p)⁻¹
  have hne : (2 : ZMod p)⁻¹ ≠ 0 := by
    intro h; rw [h, ZMod.val_zero] at h2; omega
  rcases hσ with rfl | rfl
  · exact ⟨hne, Or.inl h2⟩
  · refine ⟨neg_ne_zero.mpr hne, Or.inr ?_⟩
    erw [ZMod.neg_val]
    simp only [hne, ↓reduceIte]
    omega

/-- **`rem:onedigit`** (the antipode): `f_1(0, ±1/2) = (p-3)/(2p)` for an odd prime `p`. -/
theorem F1_zero_half (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (σ : ZMod p)
    (hσ : σ = (2 : ZMod p)⁻¹ ∨ σ = -(2 : ZMod p)⁻¹) :
    2 * gapNum1 p 0 σ = p - 3 := by
  obtain ⟨hne, hv⟩ := half_cases p hp σ hσ
  have hlt := ZMod.val_lt σ
  rw [gapNum1_eq p 0 σ hne]
  omega

/-- **`thm:WF`, arithmetic core** (coordinate `1`, one geometric digit). Let `p ≥ 5` be prime and
let the responses of coordinate `1` be frozen as in `lem:WFlaw`: `O_1^{(l)} = 0` and
`X_{1←0}^{(l)} = x ∈ {1/2, -1/2}`. For every step `e = (e_0, e_1) ∈ {-1,0,1}² ∖ {0}` the change of the
geometric digit of coordinate `1` is `σ_1 = e_0 x + e_1 · 0`, and its guaranteed gap satisfies
`f_1(e_1, σ_1) ≥ (p-3)/(2p)` (numerators: `p - 3 ≤ 2 · gapNum1`). -/
theorem WF_coord1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (e0 e1 : ℤ)
    (he0 : e0 = -1 ∨ e0 = 0 ∨ e0 = 1) (he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1)
    (hne : e0 ≠ 0 ∨ e1 ≠ 0) (x : ZMod p)
    (hx : x = (2 : ZMod p)⁻¹ ∨ x = -(2 : ZMod p)⁻¹) :
    p - 3 ≤ 2 * gapNum1 p e1 ((e0 : ZMod p) * x) := by
  rcases he0 with rfl | rfl | rfl
  · -- `σ_1 = -x`
    have hσ : -x = (2 : ZMod p)⁻¹ ∨ -x = -(2 : ZMod p)⁻¹ := by
      rcases hx with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (neg_neg _)
    obtain ⟨hn, hv⟩ := half_cases p (by omega) (-x) hσ
    have hlt := ZMod.val_lt (-x)
    have e : (((-1 : ℤ) : ZMod p) * x) = -x := by simp; rfl
    rw [e]
    rw [gapNum1_eq p e1 (-x) hn]
    rcases he1 with rfl | rfl | rfl <;> omega
  · -- `σ_1 = 0`: an axis step of coordinate `1`
    rw [show (((0 : ℤ) : ZMod p) * x) = 0 by simp, gapNum1_zero]
    rcases he1 with rfl | rfl | rfl <;> simp_all <;> omega
  · -- `σ_1 = x`
    obtain ⟨hn, hv⟩ := half_cases p (by omega) x hx
    have hlt := ZMod.val_lt x
    rw [show (((1 : ℤ) : ZMod p) * x) = x by simp, gapNum1_eq p e1 x hn]
    rcases he1 with rfl | rfl | rfl <;> omega

/-- **`thm:WF`, the certificate term** (`lem:cert` with `j = 1`, `s = 2`): under the hypotheses of
`WF_coord1`, for any change `σ_0` of the geometric digit of coordinate `0`,
`((p-3)/(2p))² ≤ f_1(e_0, σ_0)² + f_1(e_1, σ_1)²`, in numerators. -/
theorem WF_LB1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (e0 e1 : ℤ)
    (he0 : e0 = -1 ∨ e0 = 0 ∨ e0 = 1) (he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1)
    (hne : e0 ≠ 0 ∨ e1 ≠ 0) (x : ZMod p)
    (hx : x = (2 : ZMod p)⁻¹ ∨ x = -(2 : ZMod p)⁻¹) (σ0 : ZMod p) :
    (p - 3) ^ 2 ≤ 4 * (gapNum1 p e0 σ0 ^ 2 + gapNum1 p e1 ((e0 : ZMod p) * x) ^ 2) := by
  have h := WF_coord1 p hp e0 e1 he0 he1 hne x hx
  have h2 : (p - 3) ^ 2 ≤ (2 * gapNum1 p e1 ((e0 : ZMod p) * x)) ^ 2 := Nat.pow_le_pow_left h 2
  nlinarith [h2]

/-- At depth `j = 1` the general certificate numerator `gapNum` over `ℤ/qℤ` is `gapNum1`. -/
theorem gapNum_one (q : ℕ) [NeZero q] (e : ℤ) (σ : Fin 1 → ZMod q) :
    gapNum (zcode q) 1 e σ = gapNum1 q e (σ 0) := by
  unfold gapNum gapNum1
  congr 2
  ext n
  simp only [mem_image, mem_univ, true_and, encVec, Fin.sum_univ_one, Pi.add_apply]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r 0, by simp [zcode]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨fun _ => r, by simp [zcode]⟩

/-- `WF_coord1` at `p = 7` by kernel `decide` (an independent finite check; `1/2 = 4`, `-1/2 = 3`). -/
theorem WF_coord1_p7 :
    ∀ e0 ∈ ({-1, 0, 1} : Finset ℤ), ∀ e1 ∈ ({-1, 0, 1} : Finset ℤ), (e0 ≠ 0 ∨ e1 ≠ 0) →
      ∀ x ∈ ({4, 3} : Finset (ZMod 7)), 4 ≤ 2 * gapNum1 7 e1 ((e0 : ZMod 7) * x) := by
  decide

end GeoSeq
