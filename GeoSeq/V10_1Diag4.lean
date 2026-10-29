/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Sign

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 8): `thm:block`(c), `s = 4`, with the smaller free diagonal: `LB(F) = 1 - 4/p`

The design `blk4dF` keeps the off-diagonal entries of `U*_4` (so identity (a) of `def:block`, the design numerators
`blk4N` and the vanishing orders are those of `blk4`) and sets the diagonal of `F_0` to `-3` (`U*_4`: `-(5,3,5,3)`).
The diagonal is free in `def:block`. Diagonal dominance fails (rows `0` and `2` have off-diagonal sums `5`), so the
bound for large `p` uses the sign-class argument (`sc_LB`), certified by one kernel evaluation at `P = 137`
(`ca_signclass`); the primes `11 ≤ p ≤ 19` by kernel evaluations; equality by the axis step (`axis_term`).

* **`blk4d_LB_eq`**: `LB(F) = 1 - 4/p` for every prime `p ≥ 11` (instead of `1 - 6/p` for `U*_4`).
* **`blk4d_block`**: for every prime `p ≥ 11`, a digital `(0,4)`-sequence, the design relation at every `P_{16K}`, and
  `sep(P_{16K}) ≥ 1 - 4/p`.
-/

namespace GeoSeq

open Finset Polynomial

lemma blk4d_hM : ∀ j, j + 2 ≤ 4 → ∀ i c, blk4dM j i c = ∑ n ∈ range (j + 1), blk4dF n i c := by
  intro j hj; have : j ≤ 2 := by omega
  interval_cases j <;> decide +kernel

lemma blk4d_hB : ∀ j, j + 2 ≤ 4 → ∀ i c, |blk4dM j i c| ≤ blk4dB i c := by
  intro j hj; have : j ≤ 2 := by omega
  interval_cases j <;> decide +kernel

lemma blk4d_rows : (∀ i, ∑ c, blk4dB i c ≤ ((8 : ℕ) : ℤ)) ∧ ∀ i, ∑ c, blk4dB i c ≤ 63 := by decide +kernel

lemma blk4d_opts : blk4dOpts = List.ofFn fun k => caOpts blk4dM (Fin.rev k) := by decide +kernel

/-! Kernel evaluations of the checker (`A = 3`). -/

theorem blk4d_chk11 : caCheck 4 blk4dOpts blk4St0 11 3 = true := by decide +kernel
theorem blk4d_chk13 : caCheck 4 blk4dOpts blk4St0 13 3 = true := by decide +kernel
theorem blk4d_chk17 : caCheck 4 blk4dOpts blk4St0 17 3 = true := by decide +kernel
theorem blk4d_chk19 : caCheck 4 blk4dOpts blk4St0 19 3 = true := by decide +kernel
theorem blk4d_chk137 : caCheck 4 blk4dOpts blk4St0 137 3 = true := by decide +kernel

lemma prime137 : Nat.Prime 137 := by norm_num

/-- The sign-class condition for `blk4dF` with `A = 3`, from the evaluation at `P = 137`. -/
theorem blk4d_signclass : SignClass blk4dM 3 := by
  haveI : Fact (Nat.Prime 137) := ⟨prime137⟩
  refine ca_signclass (by norm_num) blk4dF blk4dM blk4d_hM blk4dB blk4d_hB 8 3 blk4d_rows.1 137 (by norm_num)
    (by norm_num) fun K => ?_
  exact caCheck_sound (p := 137) (by norm_num) blk4dF blk4dM blk4d_hM blk4dB blk4d_hB blk4d_rows.2 _ blk4d_opts _
    blk4_st0 3 (by norm_num) blk4d_chk137 K

variable {p : ℕ} [Fact p.Prime]

/-- `LB(F) ≥ 1 - 4/p` for `blk4dF` at every prime `p ≥ 11`. -/
theorem blk4d_LB (hp : 11 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 4) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  suffices key : ((p : ℝ) - ((3 : ℕ) : ℝ) - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2) by
    convert key using 2; push_cast; ring
  · by_cases h23 : 23 ≤ p
    · refine sc_LB (by norm_num) blk4dF blk4dM blk4d_hM blk4dB blk4d_hB 8 3 blk4d_rows.1 (by omega) (by norm_num)
        ?_ blk4d_signclass K e l h
      have : (23 : ℤ) ≤ p := by exact_mod_cast h23
      push_cast; nlinarith
    · have hchk : caCheck 4 blk4dOpts blk4St0 p 3 = true := by
        have hpr := (Fact.out : p.Prime)
        interval_cases p <;> first
          | (exfalso; norm_num at hpr; done)
          | with_reducible exact blk4d_chk11 | with_reducible exact blk4d_chk13
          | with_reducible exact blk4d_chk17 | with_reducible exact blk4d_chk19
      exact caCheck_sound (by norm_num) blk4dF blk4dM blk4d_hM blk4dB blk4d_hB blk4d_rows.2 _ blk4d_opts _
        blk4_st0 3 (by omega) hchk K e l h

/-- **`thm:block`(c), `s = 4`, smaller diagonal: `LB(F) = 1 - 4/p`** at every prime `p ≥ 11`: every step has a term
`≥ 1 - 4/p`, and the axis step along the place `0` (carry length `1`) has the term exactly `1 - 4/p`. -/
theorem blk4d_LB_eq (hp : 11 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 4) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 4) / p := by
  refine ⟨blk4d_LB hp K, ?_⟩
  obtain ⟨h1, h2⟩ := axis_term (p := p) (by norm_num) blk4dF blk4dM blk4d_hM 0 3 (by decide) (by omega)
    (by decide) K hK
  refine ⟨_, _, h1, ?_⟩
  rw [h2]; push_cast; ring

/-- Identity (a) of `def:block` for `blk4dF` (the off-diagonal entries are those of `U*_4`). -/
theorem blk4d_hrel (hp : 5 ≤ p) (c i : Fin 4) (h : i ≠ c) :
    wCoCo (blk4a (p := p)) c i = -C (blk4v i) *
      ∑ n ∈ range (4 - 1), C (blockF blk4dF n i c) * blk4N c (4 - 1 - n) := by
  rw [blk4_hrel hp c i h]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [blockF, blk4dF, h, and_false, if_false]

/-- **`thm:block`(c), `s = 4`, with the smaller free diagonal**: places `(0, 1, 1/2, 1/3)`, `v = (1, 1, 2, 3)`, the
design `blk4dF` (`U*_4` off the diagonal, `F_0[c][c] = -3`). For every prime `p ≥ 11` and `θ ≠ 0`: a digital
`(0,4)`-sequence, the geometric digits follow the design exactly at every full level `P_{16K}`, and
`sep(P_{16K}) ≥ 1 - 4/p` for every `K ≥ 1`. -/
theorem blk4d_block (hp : 11 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk4d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (4 * (4 * K)) →
        seqDigit (zcode p) (blk4d θ) x i (4 * K) =
          ∑ c, ∑ n ∈ range (4 - 1), blockF blk4dF n i c * seqDigit (zcode p) (blk4d θ) x c (4 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 4 (4 * K) (seqPoint (zcode p) (blk4d θ)) (((p : ℝ) - 4) / p) := by
  have ha := blk4a_injective (p := p) (by omega)
  have hv := blk4v_ne (p := p) (by omega)
  have hv1 : ∀ c, (1 : Fin 4 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := blk4_hNd (p := p) (by omega)
  have hrel := blk4d_hrel (p := p) (by omega)
  refine ⟨blockGen_t0 θ 4 blk4v _ blk4N 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq blk4a θ 4 blk4v _ blk4N 1 (zcode p) ha hθ le_rfl (by norm_num)
      hrel hv K hK i x hx, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 4) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have h := block_sep blk4a ha θ hθ 4 le_rfl (by norm_num) blk4v hv (blockF blk4dF) blk4N 1 hv1 hNd hrel K hK
    (((p : ℝ) - 4) / p) (blk4d_LB hp (4 * K))
  rwa [min_eq_right hLB1] at h

end GeoSeq
