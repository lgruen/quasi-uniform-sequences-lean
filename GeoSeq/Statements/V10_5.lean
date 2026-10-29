/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_5Defs

@[expose] public section

/-!
# Statements: stage V10_5 (paper V4, stage V10-5)

Hammersley lifts (stage V10-5, `sec:hammersley`): `prop:liftslab`(i) (the lift of a digital `(0,s)`-sequence is a `(0,m,s+1)`-net, box form and digital form with the reversal matrix first), (ii) (a slab is a digitally shifted prefix; in-slab bounds for the staggered residue, residue and block-periodic sequences via the shifted certificates); `prop:liftcarry` (the Frobenius identity, the orders of vanishing, the carry pair, the general bound in sharp and in the paper's form, the closed forms at `m = s p^r` with the sharper constant `sqrt(s+p^2)` and the paper's constants, not well separated for places `{0} u mu_(s-1)`, `mu_s`, `{0,1}`).
PROVED (`GeoSeq/V10_5Carry.lean`, `GeoSeq/V10_5Slab.lean`, `GeoSeq/V10_5SlabInst.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_5`
(definitions in `GeoSeq/V10_5Defs.lean`). Paper: V4 (`paper/sections/11-practice.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-5). Configuration:
`comparatorGeoSeqV10_5.json`.
-/

namespace GeoSeq

section G0
open Finset Matrix

theorem nat_div_eq_iff {Q : ℕ} (hQ : 0 < Q) (v a : ℕ) : v / Q = a ↔ a * Q ≤ v ∧ v < (a + 1) * Q := by
  sorry

/-- The index coordinate `v/q^m` lies in the interval `[a q^{-K_0}, (a+1) q^{-K_0})` iff `v / q^{m-K_0} = a`. -/
theorem lift_first_box {q : ℕ} (hq : 0 < q) (m K0 a v : ℕ) (hK0 : K0 ≤ m) :
    ((a : ℝ) / (q : ℝ) ^ K0 ≤ (v : ℝ) / (q : ℝ) ^ m ∧ (v : ℝ) / (q : ℝ) ^ m < ((a : ℝ) + 1) / (q : ℝ) ^ K0) ↔
      v / q ^ (m - K0) = a := by
  sorry

end G0

section G1
open Finset Matrix
variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **`prop:liftslab`(i), box form**: the Hammersley lift of a digital `(0,s)`-sequence is a `(0,m,s+1)`-net for every
`m`. -/
theorem liftNet0_of_seq0 (D : DigitCode R q) (C : Gen s R) (hseq : IsSeq0 D C) (m : ℕ) : LiftNet0 D C m := by
  sorry

theorem revMat_mulVec (m : ℕ) (w : Fin m → R) (j : Fin m) : (revMat m *ᵥ w) j = w (Fin.rev j) := by
  sorry

/-- The index coordinate of the digital lift: the reversal matrix reads the index `vecNum w` of the digit vector. -/
theorem coordE_revMat (D : DigitCode R q) (m : ℕ) (w : Fin m → R) :
    Z3NetF.coordE D.enc (revMat m) w = vecNum D m w := by
  sorry

/-- The other coordinates of the digital lift: the first `d` digits of `truncGen C m c *ᵥ w` are the cell index of the
point with index `vecNum w`. -/
theorem coordE_truncGen (D : DigitCode R q) (C : Gen s R) (m : ℕ) (w : Fin m → R) (c : Fin s) (d : ℕ)
    (hd : d ≤ m) :
    Z3NetF.coordE D.enc (truncGen C m c) w / q ^ (m - d) = cellIdx D C (vecNum D m w) c d := by
  sorry

/-- **The box form is the digital form** (`prop:liftslab`(i)): the lift is a `(0,m,s+1)`-net iff its generator
matrices `liftGen C m` (reversal matrix, then the leading blocks of the `C_c`) form a digital `(0,m,s+1)`-net. -/
theorem liftNet0_iff (D : DigitCode R q) (C : Gen s R) (m : ℕ) :
    LiftNet0 D C m ↔ Z3NetF.IsNet0E D.enc (liftGen C m) := by
  sorry

/-- **`prop:liftslab`(i)**: the Hammersley lift of a digital `(0,s)`-sequence is, for every `m`, a `(0,m,s+1)`-net
(box form) and a digital `(0,m,s+1)`-net with generator matrices `liftGen C m`: the matrix reversing the `m` index
digits for the index coordinate, the `C_c` restricted to the rows and columns `0, …, m-1` for the others. -/
theorem liftslab_i (D : DigitCode R q) (C : Gen s R) (hseq : IsSeq0 D C) (m : ℕ) :
    LiftNet0 D C m ∧ Z3NetF.IsNet0E D.enc (liftGen C m) := by
  sorry

/-- The slab `a` of `P̂_m` with `K_0` index digits consists of the indices `a q^{m-K_0} + u`, `u < q^{m-K_0}`. -/
theorem slab_mem (m K0 v : ℕ) :
    v % q ^ (m - K0) < q ^ (m - K0) ∧ v = v / q ^ (m - K0) * q ^ (m - K0) + v % q ^ (m - K0) := by
  sorry

/-- **`prop:liftslab`(ii)**: for `u < q^{m-K_0}` the index `a q^{m-K_0} + u` lies in the slab `a`; its digits are
those of `y(u)` plus the digits `ς_{c,n}` of the point `a` of the column-shifted sequence (a constant of the slab);
so in its last `s` coordinates the slab is the prefix `P_{m-K_0}` digitally shifted by `ς`. -/
theorem liftslab_ii (D : DigitCode R q) (C : Gen s R) (m K0 a u : ℕ) (hu : u < q ^ (m - K0)) :
    (a * q ^ (m - K0) + u) / q ^ (m - K0) = a ∧
    (∀ c n, seqDigit D C (a * q ^ (m - K0) + u) c n =
      seqDigit D C u c n + seqDigit D (shiftCols C (m - K0)) a c n) ∧
    ∀ c : Fin s, liftPt D C m (a * q ^ (m - K0) + u) c.succ =
      shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) u c := by
  sorry

theorem torDist2_cons_ge {d : ℕ} (x x' : ℝ) (y y' : Fin d → ℝ) :
    Z3NetDGS.torDist2 y y' ≤ Z3NetDGS.torDist2 (Fin.cons x y : Fin (d + 1) → ℝ) (Fin.cons x' y') := by
  sorry

/-- **In-slab separation** (`prop:liftslab`(ii), "every bound that `lem:shift` transfers"): if every digitally shifted
copy of `P_{m-K_0}` (by the slab constants `ς`) has distances `≥ ρ`, then any two distinct points of one slab of the
lift `P̂_m` are at toroidal distance `≥ ρ`. -/
theorem slab_sep (D : DigitCode R q) (C : Gen s R) (m K0 : ℕ) (ρ : ℝ)
    (h : ∀ a u w : ℕ, u < q ^ (m - K0) → w < q ^ (m - K0) → u ≠ w →
      ρ ≤ Z3NetDGS.torDist2 (shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) u)
        (shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) w)) :
    ∀ v w : ℕ, v / q ^ (m - K0) = w / q ^ (m - K0) → v ≠ w →
      ρ ≤ Z3NetDGS.torDist2 (liftPt D C m v) (liftPt D C m w) := by
  sorry

end G1

section G2
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- **The Frobenius identity of `prop:liftcarry`**: `∑_{t < n p^r} z^t = (z-1)^{p^r-1} (∑_{t<n} z^t)^{p^r}` in `𝔽_p[z]`
(both sides times `z - 1` are `z^{np^r} - 1 = (z^n - 1)^{p^r}`). -/
theorem liftD_identity (n r : ℕ) :
    ∑ t ∈ range (n * p ^ r), (X : (ZMod p)[X]) ^ t =
      (X - 1) ^ (p ^ r - 1) * (∑ t ∈ range n, (X : (ZMod p)[X]) ^ t) ^ (p ^ r) := by
  sorry

/-- **The orders of vanishing** (`prop:liftcarry`): `D = z^k (z-1)^{p^r-1} H^{p^r}`, `H = ∑_{t<n} z^t`, is divisible by
`(z - a)^{ord(a)}` for every place `a = 0` or `a^n = 1`: `ord(0) = k`, `ord(1) = p^r - 1`, `ord(ζ) = p^r` for
`ζ^n = 1`, `ζ ≠ 1` (`H(ζ) = 0`). -/
theorem liftD_dvd (n r k : ℕ) (a : ZMod p) (ha : a = 0 ∨ a ^ n = 1) :
    (X - C a) ^ liftOrd p r k a ∣
      X ^ k * ((X - 1) ^ (p ^ r - 1) * (∑ t ∈ range n, (X : (ZMod p)[X]) ^ t) ^ (p ^ r)) := by
  sorry

/-- The index polynomial of `∑_{t<N} b_t p^t` (digits `b_t < p`) is `∑_{t<N} b_t z^t`. -/
theorem idxPolyP_of_digits (N : ℕ) (b : ℕ → ℕ) (hb : ∀ t, b t < p) :
    idxPolyP p (∑ t ∈ range N, b t * p ^ t) = ∑ t ∈ range N, C ((b t : ℕ) : ZMod p) * X ^ t := by
  sorry

theorem idxPolyP_carryJ (k l : ℕ) : idxPolyP p (carryJ p k l) = X ^ (k + l) := by
  sorry

theorem idxPolyP_carryI (k l : ℕ) : idxPolyP p (carryI p k l) = -∑ t ∈ range l, (X : (ZMod p)[X]) ^ (k + t) := by
  sorry

/-- **The index difference** of the carry pair: `V_j - V_i = z^k (1 + z + ⋯ + z^ℓ)`. -/
theorem idxPolyP_carry_diff (k l : ℕ) :
    idxPolyP p (carryJ p k l) - idxPolyP p (carryI p k l) = X ^ k * ∑ t ∈ range (l + 1), (X : (ZMod p)[X]) ^ t := by
  sorry

end G2

section G3
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- A frame row reads Taylor coefficients: digit `n` of coordinate `c` of `scrGen a L` at `V` is
`∑_{j ≤ n} L_c[n][j] [(z - a_c)^j] V`. -/
theorem genY_scrGen (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (V : F[X]) (n : ℕ) :
    genY (scrGen a L) c V n = ∑ j ∈ range (n + 1), L c n j * (taylor (a c) V).coeff j := by
  sorry

/-- If `(z - a_c)^d ∣ V`, the first `d` digits of coordinate `c` of `V` vanish (lower-triangular `L_c`). -/
theorem genY_scrGen_vanish (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (V : F[X]) (d n : ℕ)
    (hdvd : (X - C (a c)) ^ d ∣ V) (hn : n < d) : genY (scrGen a L) c V n = 0 := by
  sorry

end G3

section G4
open Finset Polynomial

theorem torCoord_sq_le {x y B : ℝ} (h : |x - y| ≤ B) (hB : B ≤ 1) : Z3NetDGS.torCoord x y ^ 2 ≤ B ^ 2 := by
  sorry

theorem torDist2_sq {d : ℕ} (x y : Fin d → ℝ) :
    Z3NetDGS.torDist2 x y ^ 2 = ∑ j, Z3NetDGS.torCoord (x j) (y j) ^ 2 := by
  sorry

/-- `δ` of the first `N` points is at most the distance of any two of them with different positions, and `≥ 0`. -/
theorem liftDelta_le_pair {d : ℕ} (pt : ℕ → Fin d → ℝ) {N i j : ℕ} (hi : i < N) (hj : j < N) (hne : pt i ≠ pt j) :
    0 ≤ liftDelta pt N ∧ liftDelta pt N ≤ Z3NetDGS.torDist2 (pt i) (pt j) := by
  sorry

end G4

section G5
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- The lift of the sequence shifted by `0` is the lift of the sequence. -/
theorem liftPtSh_zero (C : Gen s (ZMod p)) (m : ℕ) :
    liftPtSh (zcode p) C (fun _ _ => 0) m = liftPt (zcode p) C m := by
  sorry

/-- **The carry pair of `prop:liftcarry`**: for places `a_c = 0` or `a_c^n = 1` (`n ≥ 1`), `ℓ = n p^r - 1` and
`k + n p^r ≤ m`, the indices `i = (p^ℓ - 1) p^k` and `j = p^{k+ℓ} = i + p^k` are `< p^m`, and the lifted points
(of the sequence shifted by any `ς`) satisfy `‖ŷ_i - ŷ_j‖_T² ≤ (p^k/p^m)² + ∑_c p^{-2 ord(a_c)}` with `ord(0) = k`,
`ord(1) = p^r - 1`, `ord(ζ) = p^r` otherwise (`liftOrd`). -/
theorem liftcarry_pair (a : Fin s → ZMod p) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p)
    (n r k m : ℕ) (hn : 1 ≤ n) (hA : ∀ c, a c = 0 ∨ a c ^ n = 1) (hm : k + n * p ^ r ≤ m) :
    carryI p k (n * p ^ r - 1) < p ^ m ∧ carryJ p k (n * p ^ r - 1) < p ^ m ∧
      carryJ p k (n * p ^ r - 1) = carryI p k (n * p ^ r - 1) + p ^ k ∧
      Z3NetDGS.torDist2 (liftPtSh (zcode p) (scrGen a L) ς m (carryI p k (n * p ^ r - 1)))
          (liftPtSh (zcode p) (scrGen a L) ς m (carryJ p k (n * p ^ r - 1))) ^ 2 ≤
        ((p : ℝ) ^ k / (p : ℝ) ^ m) ^ 2 + ∑ c, (1 / (p : ℝ) ^ liftOrd p r k (a c)) ^ 2 := by
  sorry

/-- **`prop:liftcarry`, sharp form** (any lower-triangular `L_c`, any digital shift, places `0` or `n`-th roots of
unity, not necessarily distinct): `δ(P̂_m)² ≤ (p^k/p^m)² + ∑_c p^{-2 ord(a_c)}`. -/
theorem liftcarry_sharp (a : Fin s → ZMod p) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p)
    (n r k m : ℕ) (hn : 1 ≤ n) (hA : ∀ c, a c = 0 ∨ a c ^ n = 1) (hm : k + n * p ^ r ≤ m) :
    0 ≤ liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) ∧
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) ^ 2 ≤
      ((p : ℝ) ^ k / (p : ℝ) ^ m) ^ 2 + ∑ c, (1 / (p : ℝ) ^ liftOrd p r k (a c)) ^ 2 := by
  sorry

/-- **`prop:liftcarry`** (as stated in the paper): a scrambled frame `C_c = L_c P_{a_c}` over `ℤ/pℤ` with distinct
places `A = {a_c} ⊆ {0} ∪ μ_n` (`n ≥ 1`), `k + n p^r ≤ m`, any digital shift:
`δ(P̂_m)² ≤ p^{2(k-m)} + [0 ∈ A] p^{-2k} + |A ∖ {0}| p^{-2(p^r-1)}`. (Neither `n ∣ p-1`, `r ≥ 1`, `k ≥ 1` nor the
nonsingularity of `L_c` is needed.) -/
theorem liftcarry (a : Fin s → ZMod p) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → ZMod p)
    (ς : Fin s → ℕ → ZMod p) (n r k m : ℕ) (hn : 1 ≤ n) (hA : ∀ c, a c = 0 ∨ a c ^ n = 1)
    (hm : k + n * p ^ r ≤ m) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) ^ 2 ≤
      ((p : ℝ) ^ k / (p : ℝ) ^ m) ^ 2 + (if (0 : ZMod p) ∈ univ.image a then 1 else 0) * (1 / (p : ℝ) ^ k) ^ 2 +
        (((univ.image a).erase 0).card : ℝ) * (1 / (p : ℝ) ^ (p ^ r - 1)) ^ 2 := by
  sorry

/-- One term of the closed forms: with `u = p^{p^r}`, `p^{-2 ord(a)} u² = 1 + [a = 1](p² - 1)` whenever `a ≠ 0` or
`k = p^r`. -/
theorem ord_term (r k : ℕ) (a : ZMod p) (hk : a = 0 → k = p ^ r) :
    (1 / (p : ℝ) ^ liftOrd p r k a) ^ 2 * ((p : ℝ) ^ (p ^ r)) ^ 2 = 1 + if a = 1 then (p : ℝ) ^ 2 - 1 else 0 := by
  sorry

/-- `∑_c (1 + [a_c = 1](p² - 1)) ≤ s + p² - 1` for distinct places. -/
theorem sum_ord_le (a : Fin s → ZMod p) (ha : Function.Injective a) :
    ∑ c, (1 + if a c = 1 then (p : ℝ) ^ 2 - 1 else 0) ≤ s + (p : ℝ) ^ 2 - 1 := by
  sorry

/-- **Closed form, places in `{0} ∪ μ_{s-1}`** (`prop:liftcarry`, first case; `s ≥ 2`, distinct places): at
`m = s p^r`, `δ(P̂_m) · p^{p^r} ≤ √(s + p²)`, i.e. `δ(P̂_m) ≤ √(s+p²) N^{-1/s}`. -/
theorem liftcarry_closed0 (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) * (p : ℝ) ^ (p ^ r) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) := by
  sorry

/-- **Closed form, places in `μ_s`** (`prop:liftcarry`, second case; distinct places): at `m = s p^r`,
`δ(P̂_m) · p^{p^r} ≤ √(s + p²)`. -/
theorem liftcarry_closedMu (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) * (p : ℝ) ^ (p ^ r) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) := by
  sorry

/-- The normalization: `x · p^{p^r} ≤ γ` gives `x · (p^{s p^r})^{1/(s+1)} ≤ γ p^{-p^r/(s+1)}`. -/
theorem norm_of_mul (r : ℕ) (x γ : ℝ) (h : x * (p : ℝ) ^ (p ^ r) ≤ γ) :
    x * ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤ γ * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  sorry

/-- **`prop:liftcarry`, normalized, places in `{0} ∪ μ_{s-1}`**: `δ(P̂_m) N^{1/(s+1)} ≤ √(s+p²) p^{-p^r/(s+1)}` at
`m = s p^r`. -/
theorem liftcarry_closed0_norm (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  sorry

/-- **`prop:liftcarry`, normalized, places in `μ_s`**: `δ(P̂_m) N^{1/(s+1)} ≤ √(s+p²) p^{-p^r/(s+1)}`. -/
theorem liftcarry_closedMu_norm (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  sorry

/-- **`prop:liftcarry`, the paper's constant for `A ⊆ {0} ∪ μ_{s-1}`**: `γ = √(2 + (s-1)p²)`. -/
theorem liftcarry_gamma0 (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (2 + ((s : ℝ) - 1) * (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  sorry

/-- **`prop:liftcarry`, the paper's constant for `A ⊆ μ_s`** (as corrected by the audit): `γ = √(1 + s p²)`. -/
theorem liftcarry_gammaMu (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (1 + (s : ℝ) * (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  sorry

/-- `γ p^{-p^r/(s+1)} < ε` for some `r`. -/
theorem exists_r_small (γ ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, γ * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) < ε := by
  sorry

/-- **The lifts are not well separated** (`prop:liftcarry`, last sentence): for distinct places in `{0} ∪ μ_{s-1}`
(`s ≥ 2`) or in `μ_s`, every lower-triangular scramble and every digital shift,
`inf_m δ(P̂_m) N^{1/(s+1)} = 0` (`N = p^m`). -/
theorem lift_not_wellsep (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : (2 ≤ s ∧ ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) ∨ ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p)
    (ς : Fin s → ℕ → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((s : ℝ) + 1)) < ε := by
  sorry

/-- **Places `{0, 1}`** (`s = 2`; every two-dimensional sequence of the paper with these places): the lifts are not
well separated, for every lower-triangular scramble and every digital shift. -/
theorem lift01_not_wellsep (a : Fin 2 → ZMod p) (ha : Function.Injective a) (hA : ∀ c, a c = 0 ∨ a c = 1)
    (L : Fin 2 → ℕ → ℕ → ZMod p) (ς : Fin 2 → ℕ → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((2 : ℕ) + 1 : ℝ)) < ε := by
  sorry

/-- The residue sequence `𝓡_v` (`def:residue`) with the places `0, 1`: its lifts are not well separated. -/
theorem lift_resSeq01_not_wellsep (a : Fin 2 → ZMod p) (ha : Function.Injective a) (hA : ∀ c, a c = 0 ∨ a c = 1)
    (θ : ZMod p) (v : Fin 2 → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPt (zcode p) (resSeq a θ v) m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((2 : ℕ) + 1 : ℝ)) < ε := by
  sorry

/-- The staggered residue sequence `𝓡^⋆_v` (`def:residuestar`, e.g. the brick wall) with the places `0, 1`: its lifts
are not well separated. -/
theorem lift_resStar01_not_wellsep (a : Fin 2 → ZMod p) (ha : Function.Injective a) (hA : ∀ c, a c = 0 ∨ a c = 1)
    (θ : ZMod p) (cs : Fin 2) (μs : ZMod p) (k : Fin 2 → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPt (zcode p) (resStar a θ cs μs k) m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((2 : ℕ) + 1 : ℝ)) < ε := by
  sorry

end G5

section G6
open Finset Polynomial
variable {q s : ℕ} [NeZero q]

/-- `lem:cert` over `ℤ/qℤ` (responses without the `l = 0` convention) for the shifted sequence. -/
theorem cert_prime_shift (C : Gen s (ZMod q)) (ς : Fin s → ℕ → ZMod q) (K j : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l → LB ≤ certTerm (zcode q) j e (certSigmaP Dr j e l)) :
    SepAtLevel q s K (shPoint (zcode q) C ς) (min 1 LB) := by
  sorry

/-- `lem:cert` with one geometric digit for the shifted sequence. -/
theorem cert_one_shift (C : Gen s (ZMod q)) (ς : Fin s → ℕ → ZMod q) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 q (e c) (∑ c', (e c' : ZMod q) * Dr (l c') c c') : ℝ) / q) ^ 2)) :
    SepAtLevel q s K (shPoint (zcode q) C ς) (min 1 LB) := by
  sorry

/-- The one-row certificate for the shifted sequence. -/
theorem cert_row_shift (C : Gen s (ZMod q)) (ς : Fin s → ℕ → ZMod q) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (c₀ : Fin s) (Drow : ℕ → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c', IsCarryEntry C K 0 l c₀ c' (Drow l c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ (gapNum1 q (e c₀) (∑ c', (e c' : ZMod q) * Drow (l c') c') : ℝ) / q) :
    SepAtLevel q s K (shPoint (zcode q) C ς) (min 1 LB) := by
  sorry

end G6

section G7
open Finset Polynomial
variable {s : ℕ} {p : ℕ}

/-- `((p^K)^{s+1})^{-1/(s+1)} = p^{-K}`. -/
theorem lift_scale (hp : 0 < p) (s K : ℕ) :
    ((p : ℝ) ^ ((s + 1) * K)) ^ (-(1 / ((s : ℝ) + 1))) = ((p : ℝ) ^ K)⁻¹ := by
  sorry

end G7

section G8
open Finset Polynomial
variable {s : ℕ} {p : ℕ} [Fact p.Prime]

/-- **`thm:residuestar` for every digitally shifted copy** (`lem:shift`): `sep(P_{sK}) ≥ β(k)`. -/
theorem residuestar_sep_shift (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (ς : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p s K (shPoint (zcode p) (resStar a θ cs μs k) ς) (betaStar p cs k) := by
  sorry

/-- **`thm:block`(iii) for every digitally shifted copy** (`lem:shift`): `sep(P_{sℓK}) ≥ min(1, LB)`. -/
theorem block_sep_shift (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (ς : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) (LB : ℝ)
    (hLB : ∀ e l, IsStep (ℓ * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2)) :
    SepAtLevel p s (ℓ * K) (shPoint (zcode p) (blockGen a θ ℓ v Fd Nd v') ς) (min 1 LB) := by
  sorry

/-- **`prop:liftslab`(ii), staggered residue sequence**: in the lift `P̂_m` of `𝓡^⋆_v` (`thm:residuestar`, `p ≥ 5`) at
`m = (s+1)K`, two distinct points of one slab with `K_0 = K` are at distance `≥ β(k) N^{-1/(s+1)}`. -/
theorem slab_residuestar (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hxy : x / p ^ ((s + 1) * K - K) = y / p ^ ((s + 1) * K - K)) (hne : x ≠ y) :
    betaStar p cs k * ((p : ℝ) ^ ((s + 1) * K)) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (resStar a θ cs μs k) ((s + 1) * K) x)
        (liftPt (zcode p) (resStar a θ cs μs k) ((s + 1) * K) y) := by
  sorry

/-- **`prop:liftslab`(ii), residue sequence**: in the lift of `𝓡_v` (`thm:residue`) at `m = (s+1)K - 1`, two distinct
points of one slab with `K_0 = K` are at distance `≥ p^{-1/(s+1)} L N^{-1/(s+1)}`, for every lower bound `L` of
`‖(|b| - 𝟏)_+‖_2` on `Λ_v ∖ {0}`. -/
theorem slab_residue (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0)
    (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b)
    (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hxy : x / p ^ ((s + 1) * K - 1 - K) = y / p ^ ((s + 1) * K - 1 - K)) (hne : x ≠ y) :
    (p : ℝ) ^ (-(1 / ((s : ℝ) + 1))) * L * ((p : ℝ) ^ ((s + 1) * K - 1)) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) x)
        (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) y) := by
  sorry

/-- `prop:liftslab`(ii) for the residue sequence with `L = ℓ_jit(Λ_v)` (the constant written in the paper). -/
theorem slab_residue_ljit (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hxy : x / p ^ ((s + 1) * K - 1 - K) = y / p ^ ((s + 1) * K - 1 - K)) (hne : x ≠ y) :
    (p : ℝ) ^ (-(1 / ((s : ℝ) + 1))) * ljit v * ((p : ℝ) ^ ((s + 1) * K - 1)) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) x)
        (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) y) := by
  sorry

/-- **`prop:liftslab`(ii), block-periodic sequence** (`thm:block`, period `ℓ = s`): in the lift at `m = s(s+1)K`,
two distinct points of one slab with `K_0 = sK` are at distance `≥ min(1, LB) N^{-1/(s+1)}` for every `LB` below the
one-digit relaxation of the design (the `LB(F)` of `thm:block`). -/
theorem slab_block (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0)
    (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (s - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (s - 1 - n))
    (K : ℕ) (hK : 1 ≤ K) (LB : ℝ)
    (hLB : ∀ e l, IsStep (s * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2))
    (x y : ℕ) (hxy : x / p ^ ((s + 1) * (s * K) - s * K) = y / p ^ ((s + 1) * (s * K) - s * K)) (hne : x ≠ y) :
    min 1 LB * ((p : ℝ) ^ ((s + 1) * (s * K))) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (blockGen a θ s v Fd Nd v') ((s + 1) * (s * K)) x)
        (liftPt (zcode p) (blockGen a θ s v Fd Nd v') ((s + 1) * (s * K)) y) := by
  sorry

end G8

end GeoSeq
