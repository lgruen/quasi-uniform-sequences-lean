/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99Blk5
public import GeoSeq.V99CovDefs

@[expose] public section

/-!
# GeoSeq stage V9-9: `thm:block`(c), `s = 5`, with the kernel evaluations as one hypothesis

`blk5_LB_ca_of`, `blk5_block_of`: the s = 5 results from `Blk5CA` (the per-prime checker evaluations). This split
lets the Comparator check the assembly and the heavy per-prime evaluations (`comparatorGeoSeqV99ca5*.json`) in separate
runs; the unconditional `blk5_block` (`GeoSeq/V99Blk5Main.lean`) is checked by `lake build`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- `thm:block`(c), `s = 5`: `LB(F) ≥ 1 - 17/p` at every prime `19 ≤ p < 84`, given the checker evaluations. -/
theorem blk5_LB_ca_of (hca : Blk5CA) (hp19 : 19 ≤ p) (hp : p < 84) (K : ℕ) : ∀ e l, IsStep K e l →
    ((p : ℝ) - 17) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) := by
  refine blk5_LB_chk (hca p ?_) (by omega) K
  have hpr := (Fact.out : p.Prime)
  interval_cases p <;> first
    | (exfalso; norm_num at hpr; done)
    | simp [blk5CAPrimes]

/-- **`thm:block`(c), `s = 5`**, given the checker evaluations `Blk5CA`: for every prime `p ≥ 19` and `θ ≠ 0`, a
digital `(0,5)`-sequence, the design relation at every `P_{25K}`, and `sep(P_{25K}) ≥ 1 - 17/p`. -/
theorem blk5_block_of (hca : Blk5CA) (hp : 19 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5 θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5F n i c * seqDigit (zcode p) (blk5 θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5 θ)) (((p : ℝ) - 17) / p) := by
  have ha := blk5a_injective (p := p) (by omega)
  have hv := blk5v_ne (p := p) (by omega)
  have hv1 : ∀ c, (1 : Fin 5 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := blk5_hNd (p := p) (by omega)
  have hrel := blk5_hrel (p := p) (by omega)
  refine ⟨blockGen_t0 θ 5 blk5v _ blk5N 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq blk5a θ 5 blk5v _ blk5N 1 (zcode p) ha hθ le_rfl (by norm_num)
      hrel hv K hK i x hx, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 17) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have h := block_sep blk5a ha θ hθ 5 le_rfl (by norm_num) blk5v hv (blockF blk5F) blk5N 1 hv1 hNd hrel K hK
    (((p : ℝ) - 17) / p) ?_
  · rwa [min_eq_right hLB1] at h
  by_cases h84 : 84 ≤ p
  · exact blk5_LB_proof h84 (5 * K)
  · exact blk5_LB_ca_of hca hp (by omega) (5 * K)

end GeoSeq
