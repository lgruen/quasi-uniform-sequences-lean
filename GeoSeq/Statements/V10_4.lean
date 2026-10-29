/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4S6Defs

@[expose] public section

/-!
# Statements: stage V10_4 (paper V4, stage V10-4)

`thm:block`(c) for every `s >= 3` (stage V10-4): `def:block`(a) from reachability over any field (existence, uniqueness, orders of vanishing), the transfer of the nets' design `U*_s` under `x -> 1/(x+1)` (from the formal `thm:A` reachability of `Z3Net/`), `a*_s >= s - 1`, the bound `1 - (a*_s+1)/p` for every prime `p >= 5 a*_s + 4`, the column of the place `0` (all ones) and the equality given `alpha_0 = a*_s`; the free diagonal for every `s` (sign-class form); the improved `s = 6` design (`U*_6` off the diagonal, diagonal `-(3,12,13,14,13,13)`): `1 - 15/p` for every prime `p >= 125` given the checker evaluation (compared separately, `comparatorGeoSeqV10_4ca<k>.json`).
PROVED (`GeoSeq/V10_4Main.lean`, `GeoSeq/V10_4Num.lean`, `GeoSeq/V10_4S6.lean`, `GeoSeq/V10_4Trans.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_4`
(definitions in `GeoSeq/V10_4S6Defs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-4). Configuration:
`comparatorGeoSeqV10_4.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F]

/-- A triangular family (`natDegree γ_n = n`, `γ_n ≠ 0` for `n ≤ M`): if `∑_{n ≤ m} x_n γ_n` has degree `≤ k`, then
`x_n = 0` for `k < n ≤ m`. -/
theorem triF_zero_above (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) (k : ℕ) :
    ∀ m, m ≤ M → ∀ x : ℕ → F, (∑ n ∈ range (m + 1), C (x n) * γ n).natDegree ≤ k →
      ∀ n, k < n → n ≤ m → x n = 0 := by
  sorry

/-- The coefficient `k` of `∑_{n ≤ m} x_n γ_n` when that sum has degree `≤ k ≤ m`: `x_k · lc(γ_k)`. -/
theorem triF_coeff (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) (k m : ℕ)
    (hm : m ≤ M) (hkm : k ≤ m) (x : ℕ → F) (hdeg : (∑ n ∈ range (m + 1), C (x n) * γ n).natDegree ≤ k) :
    (∑ n ∈ range (m + 1), C (x n) * γ n).coeff k = x k * (γ k).leadingCoeff := by
  sorry

/-- Linear independence of a triangular family. -/
theorem triF_unique (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) (m : ℕ)
    (hm : m ≤ M) (x : ℕ → F) (h0 : ∑ n ∈ range (m + 1), C (x n) * γ n = 0) : ∀ n, n ≤ m → x n = 0 := by
  sorry

/-- Expansion in a triangular family: every polynomial of degree `≤ m` is `∑_{n ≤ m} x_n γ_n`. -/
theorem triF_expand (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) :
    ∀ m, m ≤ M → ∀ h : F[X], h.natDegree ≤ m → ∃ x : ℕ → F, h = ∑ n ∈ range (m + 1), C (x n) * γ n := by
  sorry

end G0

section G1
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- A polynomial of degree `≤ s - 2` vanishing at the `s - 1` nodes `τ_{ic}`, `i ≠ c`, is zero. -/
theorem poly_zero_of_nodes (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (c : Fin s) (P : F[X])
    (hdeg : P.natDegree ≤ s - 2) (hev : ∀ i, i ≠ c → P.eval (tauF a i c) = 0) : P = 0 := by
  sorry

/-- **`def:block`(a), existence** (proof of `thm:block`(i)): for distinct places, nonzero row constants and a
reachable design, identity (a) has a solution `N_0, …, N_{s-2}` for every column, of degree `≤ s - 2`. -/
theorem designNum_exists (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ)
    (c : Fin s) : ∃ N : ℕ → F[X], IdA a v Fd c N ∧ ∀ n, (N n).natDegree ≤ s - 2 := by
  sorry

/-- **`def:block`(a), uniqueness**: two solutions of identity (a) for the column `c` agree at every depth
`n ≤ s - 2`. -/
theorem designNum_unique (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ)
    (c : Fin s) (N N' : ℕ → F[X]) (hN : IdA a v Fd c N) (hN' : IdA a v Fd c N') :
    ∀ n, n + 2 ≤ s → N n = N' n := by
  sorry

/-- **`def:block`(a), orders of vanishing** (proof of `thm:block`(i)): every solution of identity (a) for the column
`c` of a reachable design has `N_n = (z - a_c)^n N'` with `N'(a_c) ≠ 0`, `n ≤ s - 2`. -/
theorem designNum_order (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ)
    (c : Fin s) (N : ℕ → F[X]) (hN : IdA a v Fd c N) :
    ∀ n, n + 2 ≤ s → ∃ N', N n = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0 := by
  sorry

/-- **`def:block`(a) for the chosen numerators `designNd`**: identity (a) and the vanishing orders, for every
reachable design (distinct places, nonzero row constants). -/
theorem designNd_spec (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ) :
    (∀ c i, i ≠ c → wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * designNd a v Fd c (s - 1 - n)) ∧
      ∀ c n, n + 2 ≤ s → ∃ N', designNd a v Fd c (s - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0 := by
  sorry

end G1

section G2
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- The places `1/c` are distinct for `p ≥ s`. -/
theorem ustarA_injective {s : ℕ} (hsp : s ≤ p) : Function.Injective (ustarA (p := p) s) := by
  sorry

/-- The row constants `(1, 1, 2, …, s-1)` are nonzero for `p ≥ s`. -/
theorem ustarV_ne {s : ℕ} (hsp : s ≤ p) (c : Fin s) : ustarV (p := p) s c ≠ 0 := by
  sorry

/-- **The transfer of the weights**: `w̃_{ic} = v_i⁻¹ τ_{ic} (-ς_c)` at the places `a = 1/(â+1)`. -/
theorem wN_transfer {s : ℕ} (hsp : s ≤ p) {i c : Fin s} (hic : i ≠ c) :
    wNp (p := p) i c = (ustarV s i)⁻¹ * tauF (ustarA s) i c * -sgC c := by
  sorry

/-- **The transfer of the nodes**: `ỹ_{ic} = A_c(τ_{ic})`, an affine function with column-only coefficients. -/
theorem yN_transfer {s : ℕ} (hsp : s ≤ p) {i c : Fin s} (hic : i ≠ c) :
    yNp (p := p) i c = (affC c).eval (tauF (ustarA s) i c) := by
  sorry

/-- **From the nets' form to `def:block`'s reachability** (the transfer, for any design): if
`F_n[i][c] = w̃_{ic} G_{c,n}(ỹ_{ic})` (`i ≠ c`, the nets' weights and nodes at the places `∞, 0, …, s-2`, reduced
modulo `p`) with `G_{c,n}` of exact degree `n`, then the design is reachable at the places `0, 1, 1/2, …, 1/(s-1)` with
the row constants `(1, 1, 2, …, s-1)` and `γ_{c,n} = -ς_c G_{c,n}(A_c(X))`. -/
theorem reach_of_netsForm {s : ℕ} (hsp : s ≤ p) (Fd : ℕ → Fin s → Fin s → ZMod p) (G : Fin s → ℕ → (ZMod p)[X])
    (hG : ∀ c n, n + 2 ≤ s → (G c n).natDegree = n ∧ (G c n).coeff n ≠ 0)
    (hF : ∀ c i, i ≠ c → ∀ n, n + 2 ≤ s → Fd n i c = wNp i c * (G c n).eval (yNp i c)) :
    IsReachable (ustarA s) (ustarV s) Fd (fun c n => C (-sgC c) * (G c n).comp (affC c)) := by
  sorry

/-- **The proof of `thm:block`(c), "Reachability"**: for `s ≥ 3` and every prime `p ≥ s`, the nets' design `U*_s`
(`Z3NetA.UstarF s`) is reachable (`IsReachable`, `def:block`) at the places `0, 1, 1/2, …, 1/(s-1)` with the row
constants `v = (1, 1, 2, …, s-1)`. -/
theorem ustar_reachable {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) :
    ∃ γ : Fin s → ℕ → (ZMod p)[X], IsReachable (ustarA s) (ustarV s) (ustarFd s) γ := by
  sorry

end G2

section G3
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- **Identity (a) of `def:block` for `thm:block`(c)**, every `s ≥ 3` and every prime `p ≥ s`. -/
theorem ustar_hrel {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c i : Fin s) (h : i ≠ c) :
    wCoCo (ustarA (p := p) s) c i = -C (ustarV s i) *
      ∑ n ∈ range (s - 1), C (ustarFd s n i c) * ustarNd s c (s - 1 - n) := by
  sorry

/-- The vanishing orders of the design numerators of `thm:block`(c), every `s ≥ 3`, every prime `p ≥ s`. -/
theorem ustar_hNd {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c : Fin s) (n : ℕ) (hn : n + 2 ≤ s) :
    ∃ N', ustarNd (p := p) s c (s - 1 - n) = (X - C (ustarA s c)) ^ n * N' ∧ N'.eval (ustarA s c) ≠ 0 := by
  sorry

/-- **`def:block`(a), uniqueness for `thm:block`(c)**: every solution of identity (a) is `ustarNd`. -/
theorem ustar_Nd_unique {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c : Fin s) (N : ℕ → (ZMod p)[X])
    (hN : IdA (ustarA s) (ustarV s) (ustarFd s) c N) (n : ℕ) (hn : n + 2 ≤ s) :
    N n = ustarNd s c (s - 1 - n) := by
  sorry

/-- `a*_s ≥ s - 1`. -/
theorem aStar_ge {s : ℕ} [NeZero s] (hs : 3 ≤ s) : s - 1 ≤ Z3NetA.aStar s := by
  sorry

/-- **The written bound of `thm:block`(c), every `s ≥ 3`**: for every prime `p ≥ 5 a*_s + 4` every step has a term
`≥ 1 - (a*_s+1)/p`, i.e. `LB(F) ≥ 1 - (a*_s+1)/p` (diagonal dominance of `U*_s`, `dom_LB`). -/
theorem ustar_LB_proof {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hp : 5 * Z3NetA.aStar s + 4 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - Z3NetA.aStar s - 1) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c) for every `s ≥ 3`** (the written range): for every prime `p ≥ 5 a*_s + 4` and `θ ≠ 0`, the
block-periodic residue sequence with the design `U*_s` at the places `0, 1, 1/2, …, 1/(s-1)` and `v = (1, 1, 2, …, s-1)`
is a digital `(0,s)`-sequence, at every full level `P_{s²K}` the geometric digits follow the design exactly, and
`sep(P_{s²K}) ≥ 1 - (a*_s+1)/p` for every `K ≥ 1`. -/
theorem blkS_block {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hp : 5 * Z3NetA.aStar s + 4 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blkS s θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (s * K)) →
        seqDigit (zcode p) (blkS s θ) x i (s * K) =
          ∑ c, ∑ n ∈ range (s - 1), ustarFd s n i c * seqDigit (zcode p) (blkS s θ) x c (s * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p s (s * K) (seqPoint (zcode p) (blkS s θ))
        (((p : ℝ) - Z3NetA.aStar s - 1) / p) := by
  sorry

/-- The column of the place `∞` of the nets (coordinate `0`, the place `0` here) at level `0` is `(0, 1, …, 1)`:
`E_{∞,0}` is the positive generator of `Λ_0 = ℤ (0, 1, …, 1)`. -/
theorem ustar_col0 {s : ℕ} [NeZero s] (hs : 3 ≤ s) (c : Fin s) (hc : c ≠ 0) : Z3NetA.UstarF s 0 c 0 = 1 := by
  sorry

/-- **Upper bound in `thm:block`(c)**, every prime `p > a*_s + 1`: the axis step along the coordinate of the place `0`
(carry length `1`) has the term `1 - (α_0 + 1)/p`. -/
theorem blkS_axis {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hp : Z3NetA.alphaS (0 : Fin s) < p) (K : ℕ) (hK : 1 ≤ K) :
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2) =
      ((p : ℝ) - Z3NetA.alphaS (0 : Fin s) - 1) / p := by
  sorry

/-- **Equality in `thm:block`(c) for every `s ≥ 3`, conditional form**: if the row of the place `0` has the largest
`α` (`α_0 = a*_s`; the paper checks this by exact computation for `s ≤ 10`), then `LB(F) = 1 - (a*_s+1)/p` for every
prime `p ≥ 5 a*_s + 4`: every step has a term `≥ 1 - (a*_s+1)/p`, and the axis step at the place `0` attains it. -/
theorem blkS_LB_eq_of {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hmax : Z3NetA.alphaS (0 : Fin s) = Z3NetA.aStar s)
    (hp : 5 * Z3NetA.aStar s + 4 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - Z3NetA.aStar s - 1) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2) =
      ((p : ℝ) - Z3NetA.aStar s - 1) / p := by
  sorry

/-- Identity (a) for the design with the free diagonal (it does not involve the diagonal). -/
theorem ustarDiag_hrel {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (δ : Fin s → ℤ) (c i : Fin s) (h : i ≠ c) :
    wCoCo (ustarA (p := p) s) c i = -C (ustarV s i) *
      ∑ n ∈ range (s - 1), C (blockF (ustarDiagF s δ) n i c) * ustarNd s c (s - 1 - n) := by
  sorry

/-- **The free diagonal, every `s ≥ 3`**: for every diagonal `δ` (`F_0[c][c] = -δ_c`, the off-diagonal entries of
`U*_s`), every prime `p ≥ s` and `θ ≠ 0`, `blkSd s δ θ` is a digital `(0,s)`-sequence, the geometric digits follow the
design at every `P_{s²K}`, and `sep(P_{s²K}) ≥ min(1, LB)` for every lower bound `LB` of the one-digit relaxation. -/
theorem blkSd_block {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (δ : Fin s → ℤ) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blkSd s δ θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (s * K)) →
        seqDigit (zcode p) (blkSd s δ θ) x i (s * K) =
          ∑ c, ∑ n ∈ range (s - 1), blockF (ustarDiagF s δ) n i c *
            seqDigit (zcode p) (blkSd s δ θ) x c (s * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → ∀ LB : ℝ, (∀ e l, IsStep (s * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
        (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF (ustarDiagF s δ) n i c') : ℝ) / p) ^ 2)) →
        SepAtLevel p s (s * K) (seqPoint (zcode p) (blkSd s δ θ)) (min 1 LB) := by
  sorry

/-- **The free diagonal with the sign-class condition, every `s ≥ 3`**: if every step of the design `ustarDiagF s δ`
has a backward coordinate with `|σ| ≤ A` or two backward coordinates (`SignClass`, independent of `p`), then
`sep(P_{s²K}) ≥ 1 - (A+1)/p` for every prime `p ≥ s` past the threshold of `sc_LB` (`S` a bound for the row sums of
`max_j |M^{(j)}|`, `S < p`, `(p - A - 1)² ≤ 2 (p - S - 1)²`). -/
theorem blkSd_block_sc {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (δ : Fin s → ℤ) (A S : ℕ)
    (Bd : Fin s → Fin s → ℤ)
    (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Z3NetF.Msum (ustarDiagF s δ) j i c| ≤ Bd i c) (hS : ∀ i, ∑ c, Bd i c ≤ S)
    (hSp : S < p) (hAS : A ≤ S) (hq : ((p : ℤ) - A - 1) ^ 2 ≤ 2 * ((p : ℤ) - S - 1) ^ 2)
    (hcl : SignClass (Z3NetF.Msum (ustarDiagF s δ)) A) (θ : ZMod p) (hθ : θ ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p s (s * K) (seqPoint (zcode p) (blkSd s δ θ)) (((p : ℝ) - A - 1) / p) := by
  sorry

/-- **`thm:block`(i)–(iii) for every reachable design** (with the numerators `designNd` of `def:block`(a)): for
distinct places, nonzero row constants, an integer design reachable modulo `p`, and `θ ≠ 0`, the block-periodic residue
sequence with `ℓ = s` is a digital `(0,s)`-sequence, follows the design at every `P_{s²K}`, and has
`sep(P_{s²K}) ≥ min(1, LB)` for every lower bound `LB` of the one-digit relaxation. -/
theorem reach_block {s : ℕ} (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (v : Fin s → ZMod p)
    (hv : ∀ c, v c ≠ 0) (Fz : ℕ → Fin s → Fin s → ℤ) (γ : Fin s → ℕ → (ZMod p)[X])
    (hR : IsReachable a v (blockF Fz) γ) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (s * K)) →
        seqDigit (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1) x i (s * K) =
          ∑ c, ∑ n ∈ range (s - 1), blockF Fz n i c *
            seqDigit (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1) x c (s * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → ∀ LB : ℝ, (∀ e l, IsStep (s * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
        (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2)) →
        SepAtLevel p s (s * K) (seqPoint (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1))
          (min 1 LB) := by
  sorry

end G3

section G4
open Finset Polynomial

/-- The checker splits over the options of the first two coordinates (the 121 parts are evaluated in
`GeoSeq/V10_4S6ca*.lean`). -/
theorem blk6d_chk_of (h : ∀ x ∈ blk6dO0, ∀ y ∈ blk6dO1,
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + x + y) = true) :
    caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true := by
  sorry

/-- The sign-class condition for `blk6dF` with `A = 14`, from the evaluation of the checker at `P = 6367`. -/
theorem blk6d_signclass_of (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true) :
    SignClass blk6dM 14 := by
  sorry

end G4

section G5
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- The nets-form polynomials of `blk6dF` have exact degree `n` (every prime `p ≥ 5`). -/
theorem blk6G_deg (hp : 5 ≤ p) (c : Fin 6) (n : ℕ) (hn : n + 2 ≤ 6) :
    (blk6G (p := p) c n).natDegree = n ∧ (blk6G (p := p) c n).coeff n ≠ 0 := by
  sorry

/-- **The nets' form of `blk6dF`**: `F_n[i][c] = w̃_{ic} G_{c,n}(ỹ_{ic})` (`i ≠ c`), every prime `p ≥ 5`. -/
theorem blk6d_netsForm (hp : 5 ≤ p) : ∀ c i, i ≠ c → ∀ n, n + 2 ≤ 6 →
    blockF (F := ZMod p) blk6dF n i c = wNp i c * (blk6G c n).eval (yNp i c) := by
  sorry

/-- **Reachability of `blk6dF`** (`def:block`) at the places `0, 1, 1/2, …, 1/5` with `v = (1, 1, 2, 3, 4, 5)`, every
prime `p ≥ 7`. -/
theorem blk6d_reach (hp : 7 ≤ p) :
    IsReachable (ustarA (p := p) 6) (ustarV 6) (blockF blk6dF) (fun c n => C (-sgC c) * (blk6G c n).comp (affC c)) := by
  sorry

/-- `LB(F) ≥ 1 - 15/p` for `blk6dF` at every prime `p ≥ 125` (sign-class argument, `sc_LB`), given the evaluation of
the checker at `P = 6367`. -/
theorem blk6d_LB_of_chk (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true)
    (hp : 125 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 15) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **The binding configuration at a deeper carry depth**: the axis step `e = 𝟏_c` with carry lengths `j + 1`
(`j + 2 ≤ s`, `j + 1 ≤ K`) has the term `(p - α - 1)/p` if `M^{(j)}[c][c] = -α` (`α < p`) and the other entries of
column `c` of `M^{(j)}` lie in `[-1, 1]` (`axis_term` is the case `j = 0`). -/
theorem axis_term_depth {s : ℕ} (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c) (c : Fin s) (j α : ℕ) (hj : j + 2 ≤ s)
    (hα : Mz j c c = -α) (hαp : α < p) (hcol : ∀ i, i ≠ c → |Mz j i c| ≤ 1) (K : ℕ) (hK : j + 1 ≤ K) :
    IsStep K (Pi.single c 1) (fun _ => j + 1) ∧
      Real.sqrt (∑ i, ((gapNum1 p ((Pi.single c (1 : ℤ) : Fin s → ℤ) i) (∑ c', (((Pi.single c (1 : ℤ) :
        Fin s → ℤ) c' : ℤ) : ZMod p) * ∑ n ∈ range (min ((fun _ => j + 1 : Fin s → ℕ) c') (s - 1)),
          blockF Fz n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - α - 1) / p := by
  sorry

/-- **`LB(F) = 1 - 15/p` for `blk6dF`**, every prime `p ≥ 125` and every level `K ≥ 4`: every step has a term
`≥ 1 - 15/p`, and the axis step along the place `1/3` with carry length `4` attains it. -/
theorem blk6d_LB_eq_of_chk (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true)
    (hp : 125 ≤ p) (K : ℕ) (hK : 4 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 15) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 15) / p := by
  sorry

/-- **The improved `s = 6` block-periodic sequence**: places `0, 1, 1/2, …, 1/5`, `v = (1, 1, 2, 3, 4, 5)`, the design
`blk6dF` (`U*_6` off the diagonal, `F_0[c][c] = -(3, 12, 13, 14, 13, 13)`). For every prime `p ≥ 125` and `θ ≠ 0`: a
digital `(0,6)`-sequence, the design relation at every `P_{36K}`, and `sep(P_{36K}) ≥ 1 - 15/p` (`U*_6`: `1 - 44/p`,
`p ≥ 219`). -/
theorem blk6d_block_of_chk (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true)
    (hp : 125 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk6d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (6 * (6 * K)) →
        seqDigit (zcode p) (blk6d θ) x i (6 * K) =
          ∑ c, ∑ n ∈ range (6 - 1), blockF blk6dF n i c * seqDigit (zcode p) (blk6d θ) x c (6 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 6 (6 * K) (seqPoint (zcode p) (blk6d θ)) (((p : ℝ) - 15) / p) := by
  sorry

end G5

end GeoSeq
