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
# Statements: the covering half of `lem:prefix` (GeoSeq stage S5, part A)

`prefix_cov_level` (one point per closed cell of a full level), `prefix_cov`
(`h(P_{[N]}) ≤ √s q N^{-1/s}`), `prefix_mesh` (`h/δ ≤ √s q/LB` along all `N ≥ 2`). PROVED
(`GeoSeq/Mesh.lean`); the quasi-uniform clause of `thm:WF` (`WF_mesh`, earlier `cor:WF`) is in
`Statements/WF.lean`.

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset

variable {R : Type*} [CommRing R] {q s : ℕ}

/-- **`lem:prefix`, covering half (one level)**: if `P_{sK}` is a `(0,sK,s)`-net and `N ≥ q^{sK}`,
then every `x ∈ [0,1]^s` has a point of `P_{[N]}` within Euclidean distance `√s · q^{-K}`. -/
theorem prefix_cov_level [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) (N : ℕ) (hN : q ^ (s * K) ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤ Real.sqrt s / (q : ℝ) ^ K := by
  sorry

/-- **`lem:prefix`, covering half**: for a `(0,s)`-sequence, `h(P_{[N]}) ≤ √s · q · N^{-1/s}` for every
`N ≥ 1`. -/
theorem prefix_cov [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (N : ℕ) (hN : 1 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) := by
  sorry

/-- **`lem:prefix`, mesh ratio**: for a `(0,s)`-sequence with `c(P_{sK}) ≥ LB > 0` for all `K ≥ 1`,
`h(P_{[N]}) ≤ (√s q / LB) · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean covering radius,
`δ = 2 · sepRad` toroidal separation). -/
theorem prefix_mesh [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K : ℕ, 1 ≤ K → SepAtLevel q s K (seqPoint D C) LB) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q / LB *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C))) := by
  sorry

end GeoSeq
