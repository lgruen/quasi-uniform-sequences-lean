/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V99Blk4
public import GeoSeq.V99Blk5Cond
public import GeoSeq.V1Aux

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 3): equality in `thm:block`(c) for `s = 4, 5`

Stage V9-9 proved `LB(F) ≥ 1 - (a*_s + 1)/p` (`blk4_LB_proof`, `blk4_LB_ca`, `blk5_LB_proof`, `blk5_LB_ca(_of)`).
The matching upper bound needs ONE binding configuration, the same for every prime: the axis step `e = 𝟏_c` along the
coordinate `c` of the place `0` with carry length `1` (`axis_term`). Its moving coordinate is backward with
`σ_c = -α_c = -a*_s`, a term `1 - (a*_s + 1)/p`, and the other coordinates receive the entries of column `c` of `F_0`,
which lie in `{-1, 0, 1}`, so they contribute `0` (`gap_zero_small`). So the equality holds at EVERY prime at which
the lower bound holds (`p ≥ 7` for `s = 4`, `p ≥ 19` for `s = 5`), uniformly in `p`, without computation; only the
lower bound needs the kernel evaluations below the written range.

* `gap_zero_small`: `f_1(0, t) = 0` for `|t| ≤ 1`.
* **`axis_term`** (general design): the axis step along a column whose diagonal entry of `M^{(0)} = F_0` is `-α`
  (`α < p`) and whose other entries lie in `[-1, 1]` has the term `(p - α - 1)/p`.
* **`blk4_LB_eq`** (`s = 4`, every prime `p ≥ 7`): every step has a term `≥ 1 - 6/p`, and the axis step attains it,
  i.e. `LB(F) = 1 - 6/p`.
* **`blk5_LB_attained`** (`s = 5`, every prime `p ≥ 18`), **`blk5_LB_eq_proof`** (`p ≥ 84`, written range),
  **`blk5_LB_eq_of`** (`p ≥ 19`, given the kernel evaluations `Blk5CA` of stage V9-9): `LB(F) = 1 - 17/p`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- `f_1(0, t) = 0` for a non-moving coordinate with `|t| ≤ 1`. -/
lemma gap_zero_small (t : ℤ) (ht : |t| ≤ 1) : gapNum1 p 0 (t : ZMod p) = 0 := by
  have hp := (Fact.out : p.Prime).two_le
  have : Fact (1 < p) := ⟨by omega⟩
  have h1 : gapNum1 p 0 (1 : ZMod p) = 0 := by
    rw [gapNum1_eq p 0 1 one_ne_zero, ZMod.val_one]
    have : ((0 : ℤ) * p + ((1 : ℕ) : ℤ)).natAbs = 1 := by simp
    rw [this]; omega
  rcases (show t = 0 ∨ t = 1 ∨ t = -1 by rw [abs_le] at ht; omega) with rfl | rfl | rfl
  · rw [Int.cast_zero, gapNum1_zero]; simp
  · rw [Int.cast_one]; exact h1
  · rw [Int.cast_neg, Int.cast_one]
    have := gapNum1_neg p 0 (1 : ZMod p)
    rw [neg_zero] at this
    rw [this, h1]

/-- **The binding configuration** (`thm:block`(c), equality): for a design with partial sums `M^{(j)}` (`hM`), the
axis step `e = 𝟏_c` with carry lengths `1` is a step at every level `K ≥ 1`, and if `M^{(0)}[c][c] = -α` with
`α < p` and `|M^{(0)}[i][c]| ≤ 1` for `i ≠ c`, its term `(∑_i f_1(e_i, σ_i)²)^{1/2}` equals `(p - α - 1)/p`. -/
theorem axis_term {s : ℕ} (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c) (c : Fin s) (α : ℕ)
    (hα : Mz 0 c c = -α) (hαp : α < p) (hcol : ∀ i, i ≠ c → |Mz 0 i c| ≤ 1) (K : ℕ) (hK : 1 ≤ K) :
    IsStep K (Pi.single c 1) (fun _ => 1) ∧
      Real.sqrt (∑ i, ((gapNum1 p ((Pi.single c (1 : ℤ) : Fin s → ℤ) i) (∑ c', (((Pi.single c (1 : ℤ) :
        Fin s → ℤ) c' : ℤ) : ZMod p) * ∑ n ∈ range (min ((fun _ => 1 : Fin s → ℕ) c') (s - 1)),
          blockF Fz n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - α - 1) / p := by
  refine ⟨⟨fun c' => ?_, ⟨c, by simp⟩, fun _ => ⟨le_rfl, hK⟩⟩, ?_⟩
  · by_cases h : c' = c
    · subst h; simp
    · simp [h]
  simp_rw [sig_cast hs Fz Mz hM (Pi.single c 1) (fun _ => 1) (fun _ => le_rfl)]
  have hsig : ∀ i, caSig Mz (Pi.single c 1) (fun _ => 1) i = Mz 0 i c := fun i => by
    unfold caSig
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp [show min 1 (s - 1) - 1 = 0 by omega]
  have hgap : ∀ i, gapNum1 p ((Pi.single c (1 : ℤ) : Fin s → ℤ) i)
      ((caSig Mz (Pi.single c 1) (fun _ => 1) i : ℤ) : ZMod p) = if i = c then p - α - 1 else 0 := by
    intro i
    rw [hsig]
    by_cases hi : i = c
    · subst hi
      rw [if_pos rfl, Pi.single_eq_same, hα]
      have := gap_back (p := p) 1 (-α) (Or.inl rfl) (by simp) (by rw [abs_neg, Nat.abs_cast]; exact_mod_cast hαp)
      rw [abs_neg, Nat.abs_cast] at this
      omega
    · rw [if_neg hi, Pi.single_eq_of_ne hi]
      exact gap_zero_small _ (hcol i hi)
  simp_rw [hgap]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), if_pos rfl]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnn : (0 : ℝ) ≤ ((p : ℝ) - α - 1) / p := by
    apply div_nonneg _ hp0.le
    have : (α : ℝ) + 1 ≤ p := by exact_mod_cast hαp
    linarith
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  rw [Real.sqrt_sq hnn]

/-- **`thm:block`(c), `s = 4`, equality** `LB(F) = 1 - 6/p` at EVERY prime `p ≥ 7`: every step has a term
`≥ 1 - 6/p` (stage V9-9: written range `p ≥ 29`, kernel evaluations `7 ≤ p ≤ 23`), and the axis step along the place
`0` with carry length `1` has the term exactly `1 - 6/p`. -/
theorem blk4_LB_eq (hp : 7 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 6) / p := by
  refine ⟨fun e l h => ?_, ?_⟩
  · by_cases h29 : 29 ≤ p
    · exact blk4_LB_proof h29 K e l h
    · exact blk4_LB_ca hp (by omega) K e l h
  · obtain ⟨h1, h2⟩ := axis_term (p := p) (by norm_num) blk4F blk4M blk4_hM 0 5 (by decide) (by omega)
      (by decide) K hK
    refine ⟨_, _, h1, ?_⟩
    rw [h2]; push_cast; ring

/-- **`thm:block`(c), `s = 5`, the upper bound** `LB(F) ≤ 1 - 17/p` at every prime `p ≥ 18`: the axis step along the
place `0` with carry length `1` has the term exactly `1 - 17/p`. -/
theorem blk5_LB_attained (hp : 18 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p := by
  obtain ⟨h1, h2⟩ := axis_term (p := p) (by norm_num) blk5F blk5M blk5_hM 0 16 (by decide) (by omega)
    (by decide) K hK
  refine ⟨_, _, h1, ?_⟩
  rw [h2]; push_cast; ring

/-- **`thm:block`(c), `s = 5`, equality on the written range**: `LB(F) = 1 - 17/p` for every prime `p ≥ 84`. -/
theorem blk5_LB_eq_proof (hp : 84 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p :=
  ⟨blk5_LB_proof hp K, blk5_LB_attained (by omega) K hK⟩

/-- **`thm:block`(c), `s = 5`, equality** `LB(F) = 1 - 17/p` at every prime `p ≥ 19`, given the kernel evaluations
`Blk5CA` of stage V9-9 (`blk5_chk19` … `blk5_chk83`, compared separately; the unconditional form is
`blk5_LB_eq` in `GeoSeq/V10_1Blk5U.lean`). -/
theorem blk5_LB_eq_of (hca : Blk5CA) (hp : 19 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p := by
  refine ⟨fun e l h => ?_, blk5_LB_attained (by omega) K hK⟩
  by_cases h84 : 84 ≤ p
  · exact blk5_LB_proof h84 K e l h
  · exact blk5_LB_ca_of hca hp (by omega) K e l h

end GeoSeq
