/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Sep

@[expose] public section

/-!
# GeoSeq stage V9-6 (part 3): one-digit gaps for small integer changes (`rem:onedigit`)

For an integer change `t` with `|t| < p` and a step `e ∈ {-1, 0, 1}`:
* `gap_back`: a backward coordinate (`e ≠ 0`, `e t ≤ 0`) has `f_1(e, t) = (p - |t| - 1)/p`;
* `gap_fwd`: a forward coordinate (`e t > 0`) has `f_1(e, t) = (|t| - 1)/p`;
* `int_val_small`: the value `val(t mod p)` is `t` or `p + t`.
-/

namespace GeoSeq

variable {p : ℕ} [Fact p.Prime]

lemma int_val_pos (t : ℤ) (h0 : 0 ≤ t) (ht : t < p) : (((t : ZMod p)).val : ℤ) = t := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h0 ht]

lemma int_val_neg (t : ℤ) (h0 : t < 0) (ht : -(p : ℤ) < t) : (((t : ZMod p)).val : ℤ) = t + p := by
  rw [ZMod.val_intCast, ← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]

lemma int_cast_ne (t : ℤ) (h0 : t ≠ 0) (ht : |t| < p) : (t : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have := Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr h)
  omega

/-- A backward coordinate: `e ≠ 0`, `e t ≤ 0`, `|t| < p` give `f_1(e, t) = p - |t| - 1` (numerator). -/
theorem gap_back (e t : ℤ) (he : e = 1 ∨ e = -1) (het : e * t ≤ 0) (ht : |t| < p) :
    (gapNum1 p e (t : ZMod p) : ℤ) = p - |t| - 1 := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases h0 : t = 0
  · subst h0; rw [Int.cast_zero, gapNum1_zero]; rcases he with rfl | rfl <;> simp <;> omega
  · rw [gapNum1_eq p e _ (int_cast_ne t h0 ht)]
    rcases he with rfl | rfl
    · have htn : t < 0 := by omega
      have hv := int_val_neg (p := p) t htn (by rw [abs_lt] at ht; omega)
      rw [hv, abs_of_neg htn]
      generalize hA : (1 * (p : ℤ) + (t + p)).natAbs = A
      generalize hB : (1 * (p : ℤ) + (t + p) - p).natAbs = B
      have h1 : (A : ℤ) = |1 * (p : ℤ) + (t + p)| := hA ▸ Int.natCast_natAbs _
      have h2 : (B : ℤ) = |1 * (p : ℤ) + (t + p) - p| := hB ▸ Int.natCast_natAbs _
      rw [abs_of_nonneg (by omega)] at h1 h2
      have ht2 := abs_lt.mp ht
      omega
    · have htp : 0 < t := by omega
      have hv := int_val_pos (p := p) t htp.le (by rw [abs_lt] at ht; omega)
      rw [hv, abs_of_pos htp]
      generalize hA : (-1 * (p : ℤ) + t).natAbs = A
      generalize hB : (-1 * (p : ℤ) + t - p).natAbs = B
      have h1 : (A : ℤ) = |-1 * (p : ℤ) + t| := hA ▸ Int.natCast_natAbs _
      have h2 : (B : ℤ) = |-1 * (p : ℤ) + t - p| := hB ▸ Int.natCast_natAbs _
      rw [abs_of_nonpos (by rw [abs_lt] at ht; omega)] at h1 h2
      have ht2 := abs_lt.mp ht
      omega

/-- A forward coordinate: `e t > 0`, `|t| < p` give `f_1(e, t) = |t| - 1` (numerator). -/
theorem gap_fwd (e t : ℤ) (he : e = 1 ∨ e = -1) (het : 0 < e * t) (ht : |t| < p) :
    (gapNum1 p e (t : ZMod p) : ℤ) = |t| - 1 := by
  have h0 : t ≠ 0 := by rintro rfl; simp at het
  rw [gapNum1_eq p e _ (int_cast_ne t h0 ht)]
  rcases he with rfl | rfl
  · have htp : 0 < t := by omega
    have hv := int_val_pos (p := p) t htp.le (by rw [abs_lt] at ht; omega)
    rw [hv, abs_of_pos htp]
    generalize hA : (1 * (p : ℤ) + t).natAbs = A
    generalize hB : (1 * (p : ℤ) + t - p).natAbs = B
    have h1 : (A : ℤ) = |1 * (p : ℤ) + t| := hA ▸ Int.natCast_natAbs _
    have h2 : (B : ℤ) = |1 * (p : ℤ) + t - p| := hB ▸ Int.natCast_natAbs _
    rw [abs_of_nonneg (by omega)] at h1 h2
    have ht2 := abs_lt.mp ht
    omega
  · have htn : t < 0 := by omega
    have hv := int_val_neg (p := p) t htn (by rw [abs_lt] at ht; omega)
    rw [hv, abs_of_neg htn]
    generalize hA : (-1 * (p : ℤ) + (t + p)).natAbs = A
    generalize hB : (-1 * (p : ℤ) + (t + p) - p).natAbs = B
    have h1 : (A : ℤ) = |-1 * (p : ℤ) + (t + p)| := hA ▸ Int.natCast_natAbs _
    have h2 : (B : ℤ) = |-1 * (p : ℤ) + (t + p) - p| := hB ▸ Int.natCast_natAbs _
    rw [abs_of_nonpos (by omega)] at h1 h2
    have ht2 := abs_lt.mp ht
    omega

end GeoSeq
