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
# Statements: stage V99 (paper V4)

`thm:block`(c) for `s = 4` (all of it: reachability identity (a), vanishing orders, the written diagonal-dominance bound for `p ≥ 29`, kernel checks of the one-digit relaxation at every prime `7 ≤ p ≤ 109`, `sep(P_{16K}) ≥ 1 - 6/p` for every prime `p ≥ 7`) and for `s = 5` the algebra and the written bound (`p ≥ 84`); `lem:prefix` for the coverage families; `thm:coverage`(e).
PROVED (`GeoSeq/V99Blk4.lean`, `GeoSeq/V99Blk5.lean`, `GeoSeq/V99Cov.lean`, `GeoSeq/V99Gen.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **Identity (a) of `def:block` by evaluation**: for factored numerators `ndPoly a cf`, the polynomial identity
`w_{c,i} = -v_i ∑_n F_n[i][c] N_{c,s-1-n}` (`i ≠ c`) follows from its values at the places `a_j`, `j ≠ c`. -/
theorem hrel_of_eval (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (Fd : ℕ → Fin s → Fin s → F) (cf : Fin s → ℕ → ℕ → F)
    (hev : ∀ c i, i ≠ c → ∀ j, j ≠ c →
      (∏ i' : Fin s, if i' = c ∨ i' = i then 1 else (a j - a i')) =
        -(v i) * ∑ n ∈ range (s - 1), Fd n i c * ((a j - a c) ^ n *
          ∑ k ∈ range (s - 1 - n), cf c n k * a j ^ k)) :
    ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * ndPoly a cf c (s - 1 - n) := by
  sorry

/-- The vanishing orders of `def:block`(a) for factored numerators: `N_{c,s-1-n} = (z - a_c)^n N'_{c,n}` with
`N'_{c,n}(a_c) ≠ 0`, given the values `∑_k cf c n k a_c^k ≠ 0`. -/
theorem hNd_of_ndPoly (a : Fin s → F) (cf : Fin s → ℕ → ℕ → F)
    (hne : ∀ c n, n + 2 ≤ s → ∑ k ∈ range (s - 1 - n), cf c n k * a c ^ k ≠ 0) :
    ∀ c n, n + 2 ≤ s → ∃ N', ndPoly a cf c (s - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0 := by
  sorry

end G0

section G1
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **The bound of `thm:block`(c) for `p ≥ 5A + 4`** (diagonal dominance, the argument of geo `prop:D` with a jitter of
one unit): if every partial sum `M^{(j)}` has the diagonal `-α_c` and off-diagonal entries `|M^{(j)}[i][c]| ≤ B_{ic}`
with `∑_{c ≠ i} B_{ic} ≤ α_i ≤ A`, then every step has a term `≥ 1 - (A+1)/p`: an axis step along `c` has the backward
coordinate `σ_c = -e_c α_c`, and a step with two moving axes has two backward coordinates with `|σ| ≤ 2A`, and
`2 (p - 2A - 1)² ≥ (p - A - 1)²` for `p ≥ 5A + 4`. -/
theorem dom_LB (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (α : Fin s → ℤ) (Bd : Fin s → Fin s → ℤ) (A : ℕ)
    (hdiag : ∀ j, j + 2 ≤ s → ∀ i, Mz j i i = -α i)
    (hB : ∀ j, j + 2 ≤ s → ∀ i c, i ≠ c → |Mz j i c| ≤ Bd i c)
    (hdom : ∀ i, ∑ c ∈ univ.erase i, Bd i c ≤ α i) (hαA : ∀ i, α i ≤ A) (hp : 5 * A + 4 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **Soundness of the checker** (`thm:block`(c), "Small primes"): if `caCheck s opts st0 p A` evaluates to `true` (with
the literal options equal to `caOpts` of the partial sums `M^{(j)}`, all `|σ_i| ≤ 63`), then every step has a term
`≥ 1 - (A+1)/p`, i.e. the one-digit relaxation `LB(F) ≥ 1 - (A+1)/p` at this prime. -/
theorem caCheck_sound (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (Bd : Fin s → Fin s → ℤ) (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (hB63 : ∀ i, ∑ c, Bd i c ≤ 63)
    (opts : List (List (ℤ × ℤ))) (hopts : opts = List.ofFn fun k => caOpts Mz (Fin.rev k))
    (st0 : ℤ) (hst0 : st0 = caStart s) (A : ℕ) (hA : A + 1 ≤ p) (hchk : caCheck s opts st0 p A = true)
    (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2) := by
  sorry

end G1

section G2
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- **Identity (a) of `def:block` for `thm:block`(c), `s = 4`**, for every prime `p ≥ 5`. -/
theorem blk4_hrel (hp : 5 ≤ p) (c i : Fin 4) (h : i ≠ c) :
    wCoCo (blk4a (p := p)) c i = -C (blk4v i) *
      ∑ n ∈ range (4 - 1), C (blockF blk4F n i c) * blk4N c (4 - 1 - n) := by
  sorry

/-- The vanishing orders of the design numerators of `thm:block`(c), `s = 4` (every prime `p ≥ 5`). -/
theorem blk4_hNd (hp : 5 ≤ p) (c : Fin 4) (n : ℕ) (hn : n + 2 ≤ 4) :
    ∃ N', blk4N (p := p) c (4 - 1 - n) = (X - C (blk4a c)) ^ n * N' ∧ N'.eval (blk4a c) ≠ 0 := by
  sorry

/-- **`thm:block`(c), `s = 4`, proof range** (the written diagonal-dominance argument): for every prime
`p ≥ 5 a*_4 + 4 = 29` every step has a term `≥ 1 - 6/p`, i.e. `LB(F) ≥ 1 - 6/p`. -/
theorem blk4_LB_proof (hp : 29 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- The bound at one prime from one evaluation of the checker (`caCheck_sound`). -/
theorem blk4_LB_chk (hchk : caCheck 4 blk4Opts blk4St0 p 5 = true) (hp : 6 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c), `s = 4`, computer-assisted range below the proof range**: `LB(F) ≥ 1 - 6/p` at every prime
`7 ≤ p < 29`, i.e. `p = 7, 11, 13, 17, 19, 23` (kernel evaluation of `caCheck`, one per prime). -/
theorem blk4_LB_ca (hp7 : 7 ≤ p) (hp : p < 29) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c), `s = 4`, the full computer-assisted range of `tab:block`**: `LB(F) ≥ 1 - 6/p` at every prime
`7 ≤ p ≤ 109` by kernel evaluation (independently of the written argument). -/
theorem blk4_LB_ca109 (hp7 : 7 ≤ p) (hp : p ≤ 109) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c), `s = 4`**: places `(0, 1, 1/2, 1/3)`, `v = (1, 1, 2, 3)`, the design `U*_4` (`tab:block`). For
every prime `p ≥ 7` and `θ ≠ 0` the sequence is a digital `(0,4)`-sequence, at every full level `P_{16K}` the geometric
digits follow the design exactly, and `sep(P_{16K}) ≥ 1 - 6/p` for every `K ≥ 1` (`p ≥ 29`: the written argument
`blk4_LB_proof`; `7 ≤ p ≤ 23`: the kernel evaluations `blk4_LB_ca`). -/
theorem blk4_block (hp : 7 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk4 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (4 * (4 * K)) →
        seqDigit (zcode p) (blk4 θ) x i (4 * K) =
          ∑ c, ∑ n ∈ range (4 - 1), blockF blk4F n i c * seqDigit (zcode p) (blk4 θ) x c (4 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 4 (4 * K) (seqPoint (zcode p) (blk4 θ)) (((p : ℝ) - 6) / p) := by
  sorry

end G2

section G3
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- **Identity (a) of `def:block` for `thm:block`(c), `s = 5`**, for every prime `p ≥ 5`. -/
theorem blk5_hrel (hp : 5 ≤ p) (c i : Fin 5) (h : i ≠ c) :
    wCoCo (blk5a (p := p)) c i = -C (blk5v i) *
      ∑ n ∈ range (5 - 1), C (blockF blk5F n i c) * blk5N c (5 - 1 - n) := by
  sorry

/-- The vanishing orders of the design numerators of `thm:block`(c), `s = 5` (every prime `p ≥ 5`). -/
theorem blk5_hNd (hp : 5 ≤ p) (c : Fin 5) (n : ℕ) (hn : n + 2 ≤ 5) :
    ∃ N', blk5N (p := p) c (5 - 1 - n) = (X - C (blk5a c)) ^ n * N' ∧ N'.eval (blk5a c) ≠ 0 := by
  sorry

/-- **`thm:block`(c), `s = 5`, proof range** (the written diagonal-dominance argument): for every prime
`p ≥ 5 a*_5 + 4 = 84` every step has a term `≥ 1 - 17/p`, i.e. `LB(F) ≥ 1 - 17/p`. -/
theorem blk5_LB_proof (hp : 84 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- The bound at one prime from one evaluation of the checker (`caCheck_sound`). -/
theorem blk5_LB_chk (hchk : caCheck 5 blk5Opts blk5St0 p 16 = true) (hp : 17 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) := by
  sorry

end G3

section G4
open Finset

/-- `sep(P_{sK}) ≥ LB` in the level normalization (`SepAtLevel`, distances times `q^K`) gives the prefix
normalization (`SepAtPrefix`, distances times `N^{1/s}`, `N = q^{sK}`). -/
theorem prefix_of_level {q s K : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ) (LB : ℝ)
    (h : SepAtLevel q s K pt LB) : SepAtPrefix q s (s * K) pt LB := by
  sorry

theorem hasGap_sN {s : ℕ} (hs : 1 ≤ s) : HasGap (levFull s) s := by
  sorry

/-- **`lem:prefix` for `thm:coverage`**: a digital `(0,s)`-sequence with `sep(P_m) ≥ LB > 0` for every `m` of a level
family with largest gap `≤ Δ` is `Covered` (in particular quasi-uniform). -/
theorem covered_of_level {R : Type*} [CommRing R] {q s : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q)
    (hs : 1 ≤ s) (C : Gen s R) (hseq : IsSeq0 D C) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ) (LB : ℝ)
    (hLB : 0 < LB) (h : ∀ m, Lev m → SepAtPrefix q s m (seqPoint D C) LB) : Covered D s C Lev := by
  sorry

/-- Full-level bounds give `Covered` on `sℕ`. -/
theorem covered_full {R : Type*} [CommRing R] {q s : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q)
    (hs : 1 ≤ s) (C : Gen s R) (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K, 1 ≤ K → SepAtLevel q s K (seqPoint D C) LB) : Covered D s C (levFull s) := by
  sorry

/-- Bounds at every `s`-th full level give `Covered` on `s²ℕ`. -/
theorem covered_sq {R : Type*} [CommRing R] {q s : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q)
    (hs : 1 ≤ s) (C : Gen s R) (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K, 1 ≤ K → SepAtLevel q s (s * K) (seqPoint D C) LB) : Covered D s C (levSq s) := by
  sorry

end G4

section G5
open Finset
variable {p : ℕ}

/-- **`thm:coverage`(e), first sequence**: for every `s ≥ 2` and prime `p > 2^s`, the staggered residue sequence with
dyadic weights (Faure places, `θ = μ⋆ = 1`, `c⋆ = 0`, standard order; `cor:dyadic`) is `Covered` on `sℕ`. -/
theorem cov_dyadic [Fact p.Prime] {s : ℕ} (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    Covered (zcode p) s (resStar (faurePlace p) 1 ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hs⟩ 1
      (dyadicK p (stdOrder ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hs⟩))) (levFull s) := by
  sorry

/-- **`thm:coverage`(e), second sequence**: for every `s ≥ 2` and prime `p > 2^s`, the residue sequence with the
Korobov check vector (Faure places, `θ = 1`; `cor:korobov`, `cor:residueQU`) is `Covered` on `sℕ - 1`. -/
theorem cov_residue [Fact p.Prime] {s : ℕ} (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    Covered (zcode p) s (resSeq (faurePlace p) 1 (korobov p s)) (levPre s) := by
  sorry

end G5

end GeoSeq
