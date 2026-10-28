/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Defs

@[expose] public section

/-!
# Statements: stage V96 (paper V4)

Block-periodic residue sequences (`def:block` with multipliers as numerators): residue algebra and partial fractions, `thm:block`(i)–(iii) in general, the instances `thm:block`(a) (`s = 2`) and (b) (`s = 3`), `thm:blocktwo`, `prop:implied`, `cor:gauss`, the general skeleton bound and `rem:prefixcases` (`s²ℕ`).
PROVED (`GeoSeq/V96Gap.lean`, `GeoSeq/V96Gauss.lean`, `GeoSeq/V96Inst.lean`, `GeoSeq/V96Res.lean`, `GeoSeq/V96Sep.lean`, `GeoSeq/V96Two.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V96`
(definitions in `GeoSeq/V96Defs.lean`). Paper: V4 (`paper/sections/06-block.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV96.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- A common unit factor cancels: `Res_a(V A / ((z-a)^k A U)) = Res_a(V / ((z-a)^k U))`. -/
theorem locRes_cancel_unit (a : F) (k : ℕ) (V A U : F[X]) (hA : A.eval a ≠ 0) :
    locRes a k (V * A) (A * U) = locRes a k V U := by
  sorry

/-- `(z-a)^e` in the numerator lowers the pole order by `e`. -/
theorem locRes_cancel_pow (a : F) (k e : ℕ) (V U : F[X]) :
    locRes a (k + e) (V * (X - C a) ^ e) U = locRes a k V U := by
  sorry

/-- Lagrange: `∑_i w_i / w_i(a_i) = 1` for distinct places (`w_i = ∏_{i' ≠ i} (z - a_{i'})`). -/
theorem lagrange_one (a : Fin s → F) (ha : Function.Injective a) (hs : 1 ≤ s) :
    ∑ i, C ((wCo a i).eval (a i))⁻¹ * wCo a i = 1 := by
  sorry

/-- Partial fractions residue by residue: `∑_i Res_{a_c}(V u_i w^{-N} dz) / w'(a_i) = Res_{a_c}(V w^{-N-1} dz)`. -/
theorem pf_res (a : Fin s → F) (ha : Function.Injective a) (hs : 1 ≤ s) (N : ℕ) (V : F[X]) (c : Fin s) :
    ∑ i, ((wCo a i).eval (a i))⁻¹ * resAt a (stagK i N) V c = resAt a (fun _ => N + 1) V c := by
  sorry

end G0

section G1
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
  (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F)

/-- The digits of the point with index digits `f_0, …, f_{m-1}` are `blockDig` of the index polynomial. -/
theorem blockGen_vecPoly (c : Fin s) (d : ℕ) (f : ℕ → F) (m : ℕ) :
    ∑ j ∈ range m, blockGen a θ ℓ v Fd Nd v' c d j * f j = blockDig a θ ℓ v Fd Nd v' c d (vecPoly f m) := by
  sorry

end G1

section G2
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
  (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F)
variable {a}

/-- The order of vanishing of the numerators (`proof of thm:block`(i)): if every design numerator `N_{c,ℓ-1-n}`
(`n ≤ s-2`) is `(z - a_c)^n` times a unit at `a_c`, then every numerator `N_{c,j}`, `j < ℓ`, is `(z - a_c)^{ℓ-1-j}` times
a unit at `a_c`. -/
theorem blockNum_order (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hv : ∀ c, v c ≠ 0)
    (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (c : Fin s) (j : ℕ) (hj : j < ℓ) :
    ∃ N', blockNum a θ ℓ v Fd Nd v' c j = (X - C (a c)) ^ (ℓ - 1 - j) * N' ∧ N'.eval (a c) ≠ 0 := by
  sorry

/-- **`thm:block`(i)**, **`thm:blocktwo`(i)**: the block-periodic residue sequence is a digital `(0,s)`-sequence. -/
theorem blockGen_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q)
    (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s) (hv : ∀ c, v c ≠ 0)
    (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0) :
    IsSeq0 D (blockGen a θ ℓ v Fd Nd v') := by
  sorry

end G2

section G3
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
  (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F)
variable {a}
variable (a)

/-- The identity behind `thm:block`(ii) and `prop:implied` (`K ≥ 1`, any `V`): with the multiplier identities (a)
`u_i = -v_i ∑_n F_n[i][c] φ_{c,ℓ-1-n}` (`i ≠ c`), `y_{i,ℓK}(V) = ∑_c ∑_{n ≤ s-2} F_n[i][c] y_{c,ℓK-1-n}(V) +
θ^K v_i^{-1} ∑_c Res_{a_c}(V u_i w^{-ℓK} dz)` (the last sum is `[z^{-1}]` of `θ^K V u_i w^{-ℓK}`, `res_thm`). -/
theorem blockDig_own (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : Fin s) (V : F[X]) :
    blockDig a θ ℓ v Fd Nd v' i (ℓ * K) V =
      ∑ c, ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) V +
        θ ^ K * (v i)⁻¹ * ∑ c, resAt a (stagK i (ℓ * K)) V c := by
  sorry

/-- `blockDig_own` at `K = 0`: digit `0` is `y_{i,0}(V) = v_i^{-1} Res_{a_i}(V u_i dz) = v_i^{-1} V(a_i)`, written with
the residues of `V u_i` at all places (only `a_i` contributes). -/
theorem blockDig_zero (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s) (i : Fin s)
    (V : F[X]) :
    blockDig a θ ℓ v Fd Nd v' i 0 V = (v i)⁻¹ * ∑ c, resAt a (stagK i 0) V c := by
  sorry

/-- **`thm:block`(ii)**, **`thm:blocktwo`(ii)**: for `K ≥ 1`, every coordinate `i` and `deg V < m ≤ sℓK`, the
geometric digit follows the design exactly: `y_{i,ℓK}(V) = ∑_c ∑_{n ≤ s-2} F_n[i][c] y_{c,ℓK-1-n}(V)`. -/
theorem blockGen_rel (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : Fin s) (f : ℕ → F) (m : ℕ) (hm : m ≤ s * (ℓ * K)) :
    blockDig a θ ℓ v Fd Nd v' i (ℓ * K) (vecPoly f m) =
      ∑ c, ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) (vecPoly f m) := by
  sorry

/-- `thm:block`(ii) for the points: for every index `x < q^{sℓK}` (the full level `P_{sℓK}`). -/
theorem blockGen_rel_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (ha : Function.Injective a) (hθ : θ ≠ 0)
    (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : Fin s) (x : ℕ) (hx : x < q ^ (s * (ℓ * K))) :
    seqDigit D (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) =
      ∑ c, ∑ n ∈ range (s - 1), Fd n i c * seqDigit D (blockGen a θ ℓ v Fd Nd v') x c (ℓ * K - 1 - n) := by
  sorry

/-- **`thm:blocktwo`(iii)**: with `ℓ > s`, for `T = ℓn + j`, `1 ≤ j ≤ ℓ - s`, and `deg V < m`, `m + 1 ≤ s(T+1)`:
`∑_c v'_c y_{c,T}(V) = 0` (the skeleton relation of `lem:residue-rel` at level `T + 1` with the check vector `v'`). -/
theorem blockGen_skel (ha : Function.Injective a) (hv' : ∀ c, v' c ≠ 0) (n j : ℕ) (hj1 : 1 ≤ j)
    (hj : j + s ≤ ℓ) (hs : 1 ≤ s) (f : ℕ → F) (m : ℕ) (hm : m + 1 ≤ s * (ℓ * n + j + 1)) :
    ∑ c, v' c * blockDig a θ ℓ v Fd Nd v' c (ℓ * n + j) (vecPoly f m) = 0 := by
  sorry

/-- **`prop:implied`**: if `v̄_i = ξ v_i / w'(a_i)` and `v̄ᵀ F_n ≡ 0` for every `n ≤ s - 2`, then
`∑_i v̄_i y_{i,ℓK}(V) = 0` for every `K ≥ 0` and `deg V < m`, `m + 1 ≤ s(ℓK + 1)` (the skeleton relation with check vector
`v̄` at the level `s(ℓK+1) - 1`). -/
theorem blockGen_implied (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (vb : Fin s → F) (ξ : F) (hvb : ∀ i, vb i = ξ * v i / (wCo a i).eval (a i))
    (hF : ∀ n c, n + 2 ≤ s → ∑ i, vb i * Fd n i c = 0) (K : ℕ) (f : ℕ → F) (m : ℕ)
    (hm : m + 1 ≤ s * (ℓ * K + 1)) :
    ∑ i, vb i * blockDig a θ ℓ v Fd Nd v' i (ℓ * K) (vecPoly f m) = 0 := by
  sorry

end G3

section G4
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
  (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F)

/-- **The carry responses of a block-periodic sequence** at the design level `ℓK` (`thm:block`(iii)): adding `1` to the
`l` finest cell digits of coordinate `c'` changes the geometric digit of coordinate `i` by
`∑_{n < min(l, s-1)} F_n[i][c']`. -/
theorem blockGen_carry {q : ℕ} [NeZero q] (D : DigitCode F q) (ha : Function.Injective a) (hθ : θ ≠ 0)
    (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hnet : BlockNet0 D (blockGen a θ ℓ v Fd Nd v') (s * (ℓ * K)) 0) (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ ℓ * K)
    (i c' : Fin s) :
    IsCarryEntry (blockGen a θ ℓ v Fd Nd v') (ℓ * K) 0 l i c' (∑ n ∈ range (min l (s - 1)), Fd n i c') := by
  sorry

end G4

section G5
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`thm:block`(iii)**, **`thm:blocktwo`(ii)** (over `ℤ/pℤ`): with the responses `D(l) = ∑_{n < min(l,s-1)} F_n`,
`sep(P_{sℓK}) ≥ min(1, LB)` for every `K ≥ 1` and every `LB` at most the one-digit relaxation of `lem:cert`. -/
theorem block_sep (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (K : ℕ) (hK : 1 ≤ K) (LB : ℝ)
    (hLB : ∀ e l, IsStep (ℓ * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2)) :
    SepAtLevel p s (ℓ * K) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v')) (min 1 LB) := by
  sorry

/-- The fine cells of a sequence with a skeleton relation lie in `Λ_v` (`thm:residue`(i), first half, for any
digital sequence over `ℤ/pℤ`). -/
theorem skel_cells (C : Gen s (ZMod p)) (v : Fin s → ZMod p) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) (x : ℕ)
    (hx : x < p ^ (s * K - 1)) : InLat v (fun c => (cellIdx (zcode p) C x c K : ℤ)) := by
  sorry

/-- **The skeleton bound** (the proof of `thm:residue`(ii) for any digital `(0,s)`-sequence over `ℤ/pℤ`): if
`∑_c v_c y_{c,K-1}(x) = 0` for every `x < p^{sK-1}` and `L ≤ ‖(|b| - 𝟏)_+‖_2` for every `0 ≠ b ∈ Λ_v`, then any two
distinct points of `P_{sK-1}` are at toroidal distance `≥ L p^{-K}`. -/
theorem skel_sep (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (v : Fin s → ZMod p)
    (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    L ≤ (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
  sorry

/-- `skel_sep` in the paper's normalization: `sep(P_{sK-1}) ≥ p^{-1/s} L`. -/
theorem skel_sepAtPrefix (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (v : Fin s → ZMod p)
    (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) C) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  sorry

end G5

section G6
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- A backward coordinate: `e ≠ 0`, `e t ≤ 0`, `|t| < p` give `f_1(e, t) = p - |t| - 1` (numerator). -/
theorem gap_back (e t : ℤ) (he : e = 1 ∨ e = -1) (het : e * t ≤ 0) (ht : |t| < p) :
    (gapNum1 p e (t : ZMod p) : ℤ) = p - |t| - 1 := by
  sorry

/-- A forward coordinate: `e t > 0`, `|t| < p` give `f_1(e, t) = |t| - 1` (numerator). -/
theorem gap_fwd (e t : ℤ) (he : e = 1 ∨ e = -1) (het : 0 < e * t) (ht : |t| < p) :
    (gapNum1 p e (t : ZMod p) : ℤ) = |t| - 1 := by
  sorry

end G6

section G7
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- One backward moving coordinate with `|σ| ≤ 1` gives a term `≥ 1 - 2/p`. -/
theorem cert_back1 (hp : 3 ≤ p) (e : Fin s → ℤ) (σ : Fin s → ℤ) (i : Fin s) (hei : e i = 1 ∨ e i = -1)
    (het : e i * σ i ≤ 0) (hσ : |σ i| ≤ 1) :
    ((p : ℝ) - 2) / p ≤ Real.sqrt (∑ j, ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2) := by
  sorry

/-- Three backward coordinates with `|σ| ≤ 2` give a term `≥ √3 (1 - 3/p) ≥ 1 - 2/p` (`p ≥ 5`). -/
theorem cert_back3 (hp : 5 ≤ p) (e : Fin 3 → ℤ) (σ : Fin 3 → ℤ)
    (h : ∀ i, (e i = 1 ∨ e i = -1) ∧ e i * σ i ≤ 0 ∧ |σ i| ≤ 2) :
    ((p : ℝ) - 2) / p ≤ Real.sqrt (∑ j, ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2) := by
  sorry

/-- **The sign analysis of `thm:block`(a)** (exhaustive over the 8 steps, `decide`): every step has a backward moving
coordinate with `|σ| ≤ 1`. -/
theorem blk2_good : ∀ e' : Fin 2 → Fin 3, (∃ c, e' c ≠ 1) →
    ∃ i, (dec3 e' i = 1 ∨ dec3 e' i = -1) ∧ dec3 e' i * blk2sig (dec3 e') i ≤ 0 ∧
      |blk2sig (dec3 e') i| ≤ 1 := by
  sorry

/-- **`thm:block`(a)**: `s = 2`, places `(0, 1)`, `v = (1, 1)`, `F_0 = ((-1,1),(-1,-1))`. For every prime `p ≥ 3` and
`θ ≠ 0` the sequence is a digital `(0,2)`-sequence, at every full level `P_{4K}` the geometric digits follow the design
exactly, and `sep(P_{4K}) ≥ 1 - 2/p` for every `K ≥ 1`. -/
theorem blk2_block (hp : 3 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk2 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (2 * (2 * K)) →
        seqDigit (zcode p) (blk2 θ) x i (2 * K) =
          ∑ c, ∑ n ∈ range (2 - 1), blockF blk2F n i c * seqDigit (zcode p) (blk2 θ) x c (2 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 2 (2 * K) (seqPoint (zcode p) (blk2 θ)) (((p : ℝ) - 2) / p) := by
  sorry

/-- **The sign analysis of `thm:block`(b)** (exhaustive over the 26 steps and the 8 carry-length patterns, `decide`):
every step has a backward moving coordinate with `|σ| ≤ 1`, or all three coordinates are backward with `|σ| ≤ 2`. -/
theorem blk3_good : ∀ e' : Fin 3 → Fin 3, ∀ ω : Fin 3 → Bool, (∃ c, e' c ≠ 1) →
    (∃ i, (dec3 e' i = 1 ∨ dec3 e' i = -1) ∧ dec3 e' i * blk3sig (dec3 e') ω i ≤ 0 ∧
        |blk3sig (dec3 e') ω i| ≤ 1) ∨
      (∀ i, (dec3 e' i = 1 ∨ dec3 e' i = -1) ∧ dec3 e' i * blk3sig (dec3 e') ω i ≤ 0 ∧
        |blk3sig (dec3 e') ω i| ≤ 2) := by
  sorry

/-- **`thm:block`(b)**: `s = 3`, places `(0, 2, 1)`, `v = (1/2, 1/2, -1)`, `(F_0, F_1) = (M, J)`. For every prime
`p ≥ 5` and `θ ≠ 0` the sequence is a digital `(0,3)`-sequence, at every full level `P_{9K}` the geometric digits follow
the design exactly, and `sep(P_{9K}) ≥ 1 - 2/p` for every `K ≥ 1`. -/
theorem blk3_block (hp : 5 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk3 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (3 * (3 * K)) →
        seqDigit (zcode p) (blk3 θ) x i (3 * K) =
          ∑ c, ∑ n ∈ range (3 - 1), blockF blk3F n i c * seqDigit (zcode p) (blk3 θ) x c (3 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 3 (3 * K) (seqPoint (zcode p) (blk3 θ)) (((p : ℝ) - 2) / p) := by
  sorry

end G7

section G8
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`thm:blocktwo`**: a block-periodic residue sequence with block period `ℓ ≥ s`, row constants `v`, design `F`
(numerators satisfying (a) and the orders), second check vector `v'`: (i) a digital `(0,s)`-sequence; (ii) at every
design level the design relation holds and `sep(P_{sℓK}) ≥ min(1, LB)`; (iii) at every skeleton level
`m = s(T+1) - 1`, `T = ℓn + j`, `1 ≤ j ≤ ℓ - s`, the skeleton relation with `v'` holds and
`sep(P_{s(T+1)-1}) ≥ p^{-1/s} ℓ_jit(Λ_{v'})`. -/
theorem blocktwo (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n)) :
    IsSeq0 (zcode p) (blockGen a θ ℓ v Fd Nd v') ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (ℓ * K)) →
        seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) =
          ∑ c, ∑ n ∈ range (s - 1), Fd n i c * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x c (ℓ * K - 1 - n)) ∧
      (∀ K, 1 ≤ K → ∀ LB : ℝ, (∀ e l, IsStep (ℓ * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
          (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2)) →
        SepAtLevel p s (ℓ * K) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v')) (min 1 LB)) ∧
      (∀ n j, 1 ≤ j → j + s ≤ ℓ →
        (∀ x, x < p ^ (s * (ℓ * n + j + 1) - 1) →
          ∑ c, v' c * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x c (ℓ * n + j) = 0) ∧
        SepAtPrefix p s (s * (ℓ * n + j + 1) - 1) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v'))
          ((p : ℝ) ^ (-(1 / (s : ℝ))) * ljit v')) := by
  sorry

/-- **`prop:implied`** (separation): under the hypotheses of `blockGen_implied`, the skeleton relation with `v̄` holds on
`P_{s(ℓK+1)-1}` and `sep(P_{s(ℓK+1)-1}) ≥ p^{-1/s} ℓ_jit(Λ_{v̄})` for every `K ≥ 0`. -/
theorem implied_sep (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (vb : Fin s → ZMod p) (ξ : ZMod p) (hvb : ∀ i, vb i = ξ * v i / (wCo a i).eval (a i))
    (hF : ∀ n c, n + 2 ≤ s → ∑ i, vb i * Fd n i c = 0) (K : ℕ) :
    (∀ x, x < p ^ (s * (ℓ * K + 1) - 1) →
        ∑ i, vb i * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) = 0) ∧
      SepAtPrefix p s (s * (ℓ * K + 1) - 1) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v'))
        ((p : ℝ) ^ (-(1 / (s : ℝ))) * ljit vb) := by
  sorry

/-- `rem:prefixcases`, the family `s²ℕ`: every `m` has an element `s²K'` (`K' ≥ 1`) with `m < s²K' ≤ m + s²`. -/
theorem hasGap_s2N (hs : 1 ≤ s) : HasGap (fun m => ∃ K, 1 ≤ K ∧ m = s ^ 2 * K) (s ^ 2) := by
  sorry

end G8

section G9
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- The multiplier identities (a) of `cor:gauss`, over any field with `u ≠ 0`, `u² + 1 = 0`. -/
theorem gauss_hrel_gen {F : Type*} [Field F] (u : ℤ) (hu : (u : F) ≠ 0) (hsq : (u : F) ^ 2 + 1 = 0)
    (c i : Fin 2) (h : i ≠ c) :
    wCoCo (faurePl : Fin 2 → F) c i = -C ((![-(u : F), -1] : Fin 2 → F) i) *
      ∑ n ∈ range (2 - 1), C (blockF (gaussF u) n i c) * gaussN (u : F) c (2 - 1 - n) := by
  sorry

/-- **`cor:gauss`, the design levels** (one-digit relaxation): every step has a term
`≥ √((u-2)² + (u²-u-1)²)/p`. -/
theorem gauss_LB (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (K : ℕ) (e : Fin 2 → ℤ) (l : Fin 2 → ℕ)
    (hst : IsStep (2 * K) e l) :
    Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (2 - 1)), blockF (gaussF u) n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **The lattice of `cor:gauss`**: for `p = u² + 1` every nonzero `b ∈ Λ_{(u,-1)} = {u b_0 ≡ b_1}` has
`‖(|b| - 𝟏)_+‖_2 ≥ u - 1` (`Λ = ℤ(1,u) + ℤ(u,-1)`, `|b|² = (m² + n²) p`). -/
theorem gauss_lattice (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (b : Fin 2 → ℤ) (hb : b ≠ 0)
    (hlat : InLat (![((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) b) : (u : ℝ) - 1 ≤ jitNorm b := by
  sorry

/-- The implied-relation data of `cor:gauss` over any field: `v̄ = (u, -1)` satisfies `v̄_i = v_i / w'(a_i)` and
`v̄ᵀ F_0 = 0` (using `u² + 1 = 0`). -/
theorem gauss_implied_gen {F : Type*} [Field F] (u : ℤ) (hsq : (u : F) ^ 2 + 1 = 0) :
    (∀ i, (![(u : F), -1] : Fin 2 → F) i = 1 * (![-(u : F), -1] : Fin 2 → F) i /
      (wCo (faurePl : Fin 2 → F) i).eval (faurePl i)) ∧
    (∀ n c, n + 2 ≤ 2 → ∑ i, (![(u : F), -1] : Fin 2 → F) i * blockF (gaussF u) n i c = 0) := by
  sorry

/-- **`cor:gauss`**: let `p = u² + 1` be prime (`u ≥ 2`), `θ ≠ 0`. The block-periodic residue sequence with
`s = ℓ = 2`, places `(0, 1)`, `v = (-u, -1)`, `F_0 = ((-1, u), (-u, -1))` is a digital `(0,2)`-sequence with
`sep(P_{4K}) ≥ √((u-2)² + (u²-u-1)²)/p ≥ 1 - (u+2)/p` for every `K ≥ 1` (`u = √(p-1)`), and at every level `4K + 1`
the skeleton relation with `v̄ = (u, -1)` holds and `sep(P_{4K+1}) ≥ (u-1)/√p`. -/
theorem gauss (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (gaussGen u θ) ∧
      (∀ K, 1 ≤ K → SepAtLevel p 2 (2 * K) (seqPoint (zcode p) (gaussGen u θ))
        (Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p)) ∧
      1 - ((u : ℝ) + 2) / p ≤ Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ∧
      ∀ K, (∀ x, x < p ^ (2 * (2 * K + 1) - 1) →
          ∑ i, (![((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) i *
            seqDigit (zcode p) (gaussGen u θ) x i (2 * K) = 0) ∧
        SepAtPrefix p 2 (2 * (2 * K + 1) - 1) (seqPoint (zcode p) (gaussGen u θ))
          ((p : ℝ) ^ (-(1 / ((2 : ℕ) : ℝ))) * ((u : ℝ) - 1)) := by
  sorry

end G9

end GeoSeq
