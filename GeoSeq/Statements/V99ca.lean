/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99CovDefs

@[expose] public section

/-!
# Statements: stage V99ca (paper V4)

`thm:block`(c) for `s = 5` from the kernel evaluations of the one-digit relaxation at the primes `19 ≤ p ≤ 83` (hypothesis `Blk5CA`; the evaluations are compared in `comparatorGeoSeqV99ca5a..d.json`): `sep(P_{25K}) ≥ 1 - 17/p` for every prime `p ≥ 19`.
PROVED (`GeoSeq/V99Blk5Cond.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99ca`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99ca.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- `thm:block`(c), `s = 5`: `LB(F) ≥ 1 - 17/p` at every prime `19 ≤ p < 84`, given the checker evaluations. -/
theorem blk5_LB_ca_of (hca : Blk5CA) (hp19 : 19 ≤ p) (hp : p < 84) (K : ℕ) : ∀ e l, IsStep K e l →
    ((p : ℝ) - 17) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c), `s = 5`**, given the checker evaluations `Blk5CA`: for every prime `p ≥ 19` and `θ ≠ 0`, a
digital `(0,5)`-sequence, the design relation at every `P_{25K}`, and `sep(P_{25K}) ≥ 1 - 17/p`. -/
theorem blk5_block_of (hca : Blk5CA) (hp : 19 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5 θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5F n i c * seqDigit (zcode p) (blk5 θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5 θ)) (((p : ℝ) - 17) / p) := by
  sorry

end G0

end GeoSeq
