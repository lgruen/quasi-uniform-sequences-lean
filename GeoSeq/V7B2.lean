/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B2Cert
public import GeoSeq.Mesh
public import Z3Net.DGS

@[expose] public section

/-!
# GeoSeq stage V7: the `κ_m` side claim of `thm:B2`

**`B2_kappa`**: every prefix `P_m = {y(v) : v < 2^m}` of the base-two sequence of `thm:B2` is `κ_m`-separated in
the sense of [DGS2] (Def. 3.3: every shifted dyadic elementary square of side `2^{-κ_m}` contains at most one
point; `Z3NetDGS.IsKSep`), and also toroidally `κ_m`-separated (`Z3NetDGS.IsKSepTor`), with
`κ_m = ⌈m/2⌉ + 3`. Proof as in the paper: two points in a square of side `2^{-κ}` are less than `√2 · 2^{-κ}` apart
(toroidally), and `√2 · 2^{-⌈m/2⌉-3} < 0.1839 · 2^{-m/2} ≤ δ(P_m)` (`B2_allN`); [DGS2, Lemma 3.7] in the form
`Z3NetDGS.Proofs.lemma37`.
-/

namespace GeoSeq

/-- **`thm:B2`, `κ_m`-separation**: for every `m`, the prefix `P_m` (the first `2^m` points) of the sequence of
`thm:B2` is `κ_m`-separated and toroidally `κ_m`-separated in base `2` in the sense of [DGS2], `κ_m = ⌈m/2⌉ + 3`
(`⌈m/2⌉ = (m+1)/2` in `ℕ`). -/
theorem B2_kappa (m : ℕ) :
    Z3NetDGS.IsKSep 2 ((m + 1) / 2 + 3) (prefixSet (2 ^ m) (seqPoint (zcode 2) B2gen)) ∧
      Z3NetDGS.IsKSepTor 2 ((m + 1) / 2 + 3) (prefixSet (2 ^ m) (seqPoint (zcode 2) B2gen)) := by
  set k := (m + 1) / 2 with hk
  apply Z3NetDGS.Proofs.lemma37 2 (k + 3) le_rfl
  intro x hx y hy hxy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  have hvw : v ≠ w := fun h => hxy (by rw [h])
  rw [Finset.mem_range] at hv hw
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hv hw; omega
    · exact h
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hsep := B2_allN (2 ^ m) h2m v w hv hw hvw
  -- coordinates in `[0,1]`
  have hunit : ∀ u (c : Fin 2), 0 ≤ seqPoint (zcode 2) B2gen u c ∧ seqPoint (zcode 2) B2gen u c ≤ 1 := by
    intro u c
    have := coord_cell (by norm_num) (zcode 2) B2gen u c 0
    simp only [pow_zero, one_mul] at this
    have h0 : cellIdx (zcode 2) B2gen u c 0 = 0 := by simp [cellIdx]
    rw [h0] at this
    push_cast at this
    exact ⟨this.1, by linarith [this.2]⟩
  by_contra hall
  push_neg at hall
  have hQ : (0 : ℝ) < (2 : ℝ) ^ (k + 3) := by positivity
  have ht : ∀ j : Fin 2, Z3NetDGS.torCoord (seqPoint (zcode 2) B2gen v j) (seqPoint (zcode 2) B2gen w j) ^ 2 <
      (1 / (2 : ℝ) ^ (k + 3)) ^ 2 := by
    intro j
    have h0 : 0 ≤ Z3NetDGS.torCoord (seqPoint (zcode 2) B2gen v j) (seqPoint (zcode 2) B2gen w j) := by
      unfold Z3NetDGS.torCoord
      have a1 := hunit v j; have a2 := hunit w j
      apply le_min (abs_nonneg _)
      rw [sub_nonneg, abs_le]; constructor <;> linarith
    have := hall j
    push_cast at this
    exact pow_lt_pow_left₀ this h0 (by norm_num)
  have hlt : Z3NetDGS.torDist2 (seqPoint (zcode 2) B2gen v) (seqPoint (zcode 2) B2gen w) <
      Real.sqrt 2 / (2 : ℝ) ^ (k + 3) := by
    unfold Z3NetDGS.torDist2
    rw [Fin.sum_univ_two]
    have e : Real.sqrt 2 / (2 : ℝ) ^ (k + 3) = Real.sqrt (2 * (1 / (2 : ℝ) ^ (k + 3)) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]; ring
    rw [e]
    apply Real.sqrt_lt_sqrt (by positivity)
    linarith [ht 0, ht 1]
  -- `(2^m)^{-1/2} ≥ 2^{-k}`
  have hA : ((2 : ℝ) ^ k)⁻¹ ≤ (((2 ^ m : ℕ) : ℝ)) ^ (-(1 / ((2 : ℕ) : ℝ))) := by
    have hpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
    rw [Real.rpow_neg hpos.le]
    apply inv_anti₀ (by positivity)
    have e1 : ((2 : ℝ) ^ k) = (((2 : ℝ) ^ k) ^ 2) ^ ((2 : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) (by norm_num)).symm
    rw [e1]
    push_cast
    rw [one_div]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hs2 : Real.sqrt 2 < 14712 / 10000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h8 : Real.sqrt 2 / (2 : ℝ) ^ (k + 3) ≤ 1839 / 10000 * ((2 : ℝ) ^ k)⁻¹ := by
    rw [pow_add, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    field_simp
    nlinarith
  have := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 1839 / 10000)
  linarith

end GeoSeq
