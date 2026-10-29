/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1D5big
public import GeoSeq.V99Blk5

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 10): `thm:block`(c), `s = 5`, with the smaller free diagonal: `LB(F) = 1 - 8/p`

The design `blk5dF` keeps the off-diagonal entries of `U*_5` (identity (a), the numerators `blk5N` and the vanishing
orders are those of `blk5`) and sets the diagonal of `F_0` to `-7` (`U*_5`: `-(16,8,12,12,7)`).

* `blk5d_signclass` (from the evaluation at `P = 1361`), **`blk5d_LB_proof`**: `LB(F) ≥ 1 - 8/p` for every prime
  `p ≥ 67` (sign-class argument, `sc_LB`).
* `blk5d_LB_attained`: the axis step along the place `0` has the term `1 - 8/p` (every prime `p ≥ 9`).
* **`blk5d_LB_eq_of`**, **`blk5d_block_of`** (`p ≥ 23`, given the kernel evaluations `Blk5dCA` at `23 ≤ p ≤ 61`,
  `GeoSeq/V10_1D5ca*.lean`); the unconditional forms are in `GeoSeq/V10_1D5Main.lean` (`lake build` only).
-/

namespace GeoSeq

open Finset Polynomial

lemma blk5d_hM : ∀ j, j + 2 ≤ 5 → ∀ i c, blk5dM j i c = ∑ n ∈ range (j + 1), blk5dF n i c := by
  intro j hj; have : j ≤ 3 := by omega
  interval_cases j <;> decide +kernel

lemma blk5d_hB : ∀ j, j + 2 ≤ 5 → ∀ i c, |blk5dM j i c| ≤ blk5dB i c := by
  intro j hj; have : j ≤ 3 := by omega
  interval_cases j <;> decide +kernel

lemma blk5d_rows : (∀ i, ∑ c, blk5dB i c ≤ ((23 : ℕ) : ℤ)) ∧ ∀ i, ∑ c, blk5dB i c ≤ 63 := by decide +kernel

lemma blk5d_opts : blk5dOpts = List.ofFn fun k => caOpts blk5dM (Fin.rev k) := by decide +kernel

lemma prime1361 : Nat.Prime 1361 := by norm_num

/-- The sign-class condition for `blk5dF` with `A = 7`, from the evaluation at `P = 1361`. -/
theorem blk5d_signclass : SignClass blk5dM 7 := by
  haveI : Fact (Nat.Prime 1361) := ⟨prime1361⟩
  refine ca_signclass (by norm_num) blk5dF blk5dM blk5d_hM blk5dB blk5d_hB 23 7 blk5d_rows.1 1361 (by norm_num)
    (by norm_num) fun K => ?_
  exact caCheck_sound (p := 1361) (by norm_num) blk5dF blk5dM blk5d_hM blk5dB blk5d_hB blk5d_rows.2 _ blk5d_opts _
    blk5_st0 7 (by norm_num) blk5d_chk1361 K

variable {p : ℕ} [Fact p.Prime]

/-- `LB(F) ≥ 1 - 8/p` for `blk5dF` at every prime `p ≥ 67` (sign-class argument). -/
theorem blk5d_LB_proof (hp : 67 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  suffices key : ((p : ℝ) - ((7 : ℕ) : ℝ) - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) by
    convert key using 2; push_cast; ring
  refine sc_LB (by norm_num) blk5dF blk5dM blk5d_hM blk5dB blk5d_hB 23 7 blk5d_rows.1 (by omega) (by norm_num)
    ?_ blk5d_signclass K e l h
  have : (67 : ℤ) ≤ p := by exact_mod_cast hp
  push_cast; nlinarith

/-- The bound at one prime from one evaluation of the checker. -/
theorem blk5d_LB_chk (hchk : caCheck 5 blk5dOpts blk5St0 p 7 = true) (hp : 8 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  have := caCheck_sound (p := p) (by norm_num) blk5dF blk5dM blk5d_hM blk5dB blk5d_hB blk5d_rows.2 _ blk5d_opts _
    blk5_st0 7 (by omega) hchk K e l h
  convert this using 2; push_cast; ring

/-- The axis step along the place `0` (carry length `1`) has the term `1 - 8/p` (every prime `p ≥ 9`). -/
theorem blk5d_LB_attained (hp : 9 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 8) / p := by
  obtain ⟨h1, h2⟩ := axis_term (p := p) (by norm_num) blk5dF blk5dM blk5d_hM 0 7 (by decide) (by omega)
    (by decide) K hK
  refine ⟨_, _, h1, ?_⟩
  rw [h2]; push_cast; ring

/-- `LB(F) ≥ 1 - 8/p` at every prime `p ≥ 23`, given the kernel evaluations `Blk5dCA` (`23 ≤ p ≤ 61`). -/
theorem blk5d_LB_of (hca : Blk5dCA) (hp : 23 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) := by
  by_cases h67 : 67 ≤ p
  · exact blk5d_LB_proof h67 K
  · refine blk5d_LB_chk (hca p ?_) (by omega) K
    have hpr := (Fact.out : p.Prime)
    interval_cases p <;> first
      | (exfalso; norm_num at hpr; done)
      | simp [blk5dCAPrimes]

/-- **`thm:block`(c), `s = 5`, smaller diagonal: `LB(F) = 1 - 8/p`** at every prime `p ≥ 23`, given `Blk5dCA`. -/
theorem blk5d_LB_eq_of (hca : Blk5dCA) (hp : 23 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 8) / p :=
  ⟨blk5d_LB_of hca hp K, blk5d_LB_attained (by omega) K hK⟩

/-- Identity (a) of `def:block` for `blk5dF` (the off-diagonal entries are those of `U*_5`). -/
theorem blk5d_hrel (hp : 5 ≤ p) (c i : Fin 5) (h : i ≠ c) :
    wCoCo (blk5a (p := p)) c i = -C (blk5v i) *
      ∑ n ∈ range (5 - 1), C (blockF blk5dF n i c) * blk5N c (5 - 1 - n) := by
  rw [blk5_hrel hp c i h]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [blockF, blk5dF, h, and_false, ite_false]

/-- The sequence part of `thm:block` for `blk5dF` from any bound `LB` on the steps. -/
theorem blk5d_block_gen (hp : 5 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) (LB : ℝ) (hLB1 : LB ≤ 1)
    (hLB : ∀ K e l, IsStep K e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2)) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) LB := by
  have ha := blk5a_injective (p := p) hp
  have hv := blk5v_ne (p := p) hp
  have hv1 : ∀ c, (1 : Fin 5 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := blk5_hNd (p := p) hp
  have hrel := blk5d_hrel (p := p) hp
  refine ⟨blockGen_t0 θ 5 blk5v _ blk5N 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq blk5a θ 5 blk5v _ blk5N 1 (zcode p) ha hθ le_rfl (by norm_num)
      hrel hv K hK i x hx, fun K hK => ?_⟩
  have h := block_sep blk5a ha θ hθ 5 le_rfl (by norm_num) blk5v hv (blockF blk5dF) blk5N 1 hv1 hNd hrel K hK
    LB (hLB (5 * K))
  rwa [min_eq_right hLB1] at h

/-- **`thm:block`(c), `s = 5`, with the smaller free diagonal**, given `Blk5dCA`: places `(0, 1, 1/2, 1/3, 1/4)`,
`v = (1, 1, 2, 3, 4)`, the design `blk5dF` (`U*_5` off the diagonal, `F_0[c][c] = -7`). For every prime `p ≥ 23` and
`θ ≠ 0`: a digital `(0,5)`-sequence, the design relation at every `P_{25K}`, and `sep(P_{25K}) ≥ 1 - 8/p`. -/
theorem blk5d_block_of (hca : Blk5dCA) (hp : 23 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) (((p : ℝ) - 8) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  refine blk5d_block_gen (by omega) θ hθ _ (by rw [div_le_one hp0]; linarith) fun K => blk5d_LB_of hca hp K

/-- **`thm:block`(c), `s = 5`, smaller diagonal, written range**: for every prime `p ≥ 67` and `θ ≠ 0`, the sequence
part with `sep(P_{25K}) ≥ 1 - 8/p` (no kernel evaluation below `p = 67` needed). -/
theorem blk5d_block_proof (hp : 67 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) (((p : ℝ) - 8) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  refine blk5d_block_gen (by omega) θ hθ _ (by rw [div_le_one hp0]; linarith) fun K => blk5d_LB_proof hp K

end GeoSeq
