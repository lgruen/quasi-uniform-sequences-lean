/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Diag5
public import GeoSeq.V10_1D5caa
public import GeoSeq.V10_1D5cab
public import GeoSeq.V10_1D5cac

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 11): `thm:block`(c), `s = 5`, smaller diagonal, unconditional

`blk5d_CA` assembles the ten kernel evaluations; `blk5d_block`, `blk5d_LB_eq` for every prime `p ≥ 23`. Checked by
`lake build` (the closure contains the ten evaluations, compared separately one prime per configuration).
-/

namespace GeoSeq

open Finset Polynomial

/-- The kernel evaluations at the primes `23 ≤ p ≤ 61`. -/
theorem blk5d_CA : Blk5dCA := by
  intro q hq
  simp only [blk5dCAPrimes, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact blk5d_chk23
  · exact blk5d_chk29
  · exact blk5d_chk31
  · exact blk5d_chk37
  · exact blk5d_chk41
  · exact blk5d_chk43
  · exact blk5d_chk47
  · exact blk5d_chk53
  · exact blk5d_chk59
  · exact blk5d_chk61

variable {p : ℕ} [Fact p.Prime]

/-- **`thm:block`(c), `s = 5`, smaller diagonal**: for every prime `p ≥ 23` and `θ ≠ 0`, a digital `(0,5)`-sequence,
the design relation at every `P_{25K}`, and `sep(P_{25K}) ≥ 1 - 8/p`. -/
theorem blk5d_block (hp : 23 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) (((p : ℝ) - 8) / p) :=
  blk5d_block_of blk5d_CA hp θ hθ

/-- **`thm:block`(c), `s = 5`, smaller diagonal: `LB(F) = 1 - 8/p`** at every prime `p ≥ 23`. -/
theorem blk5d_LB_eq (hp : 23 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 8) / p :=
  blk5d_LB_eq_of blk5d_CA hp K hK

end GeoSeq
