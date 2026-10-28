/-
Copyright (c) 2026 Leonhard Gruenschloss. Released under the MIT license.
Author: Leonhard Gruenschloss.
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital sequences in every dimension" (geoseq
paper, version V4), Corollary `cor:halton` of Theorem `thm:nonqu`, and Theorem `thm:residue` with
`cor:korobov`, `cor:residueQU` (results cited by `\label`, never by number).
The constructions, proofs and Lean formalization were produced by AI systems (Anthropic Claude)
under the author's direction; responsibility rests with the author.
-/
module
public import Mathlib

@[expose] public section

/-!
# Why the classical sequences fail, and a quasi-uniform fix in every dimension

**Fail** (`cor:halton`; Goda–Hofer–Suzuki, Open Problem 2). Let `p` be a prime, `s ≥ 2`, and let
`b_0, …, b_{s-1} ∈ 𝔽_p[z]` be pairwise coprime of degrees `≥ 1` (not necessarily monic or irreducible).
The Halton-type sequence in these bases (Goda–Hofer–Suzuki, Def. 2; paper `def:radinv`) is not
quasi-uniform, and for every `ε > 0` some prefix of `p^m` points contains two points at Euclidean distance
`< ε p^{-m/s}`.

**Fix** (`thm:residue`, `cor:korobov`, `cor:residueQU`). Let `s ≥ 2`, `p > 2^s` prime, `ρ = ⌊p^{1/s}⌋`.
The residue sequence `𝓡_v` (`def:residue`) with the Faure places `a_c = c`, scale `θ = 1` and the Korobov
check vector `v = (ρ, ρ², …, ρ^{s-1}, -1)`, i.e. `C_c[n][i] = v_c^{-1} [(z - a_c)^n] z^i / w_c(z)^{n+1}` with
`w_c = ∏_{c'≠c}(z - a_{c'})` (`resGen`), is a digital `(0,s)`-sequence over `𝔽_p`; for every `K ≥ 1` any two
distinct points among its first `N = p^{sK-1}` points have toroidal Euclidean distance at least
`(ρ - 1) p^{-1/s} N^{-1/s}` (`sep(P_{sK-1}) ≥ (ρ - 1) p^{-1/s}`); and the sequence is quasi-uniform.

**Reading the definitions.**
* *Digital sequences* (`sec:prelim`). `C c n k ∈ 𝔽_p` is row `n` (output digit, `0` most significant) and
  column `k` (index digit) of `C_c`. The point with index `v = ∑ v_k p^k` has digits
  `y_{c,n}(v) = ∑_k C_c[n][k] v_k` and coordinates `y_c(v) = ∑_n y_{c,n}(v) p^{-n-1}` (`seqPoint`; a digit
  `y ∈ 𝔽_p` is read as `y.val ∈ {0, …, p-1}`).
* *`(0,s)`-sequence* (`IsSeq0`): for all `m, k`, the points with indices `k p^m ≤ v < (k+1) p^m` form a
  `(0,m,s)`-net: every elementary box with `d_c` digits in coordinate `c` (`∑_c d_c = m`) contains exactly
  one of them. Box membership is read off the digits (`cellIdx`), as in the paper.
* *Halton-type sequence* (`haltonPt`). The index `n = ∑_k n_k p^k` is the polynomial `V = ∑_k n_k z^k`
  (`idxPoly`). Coordinate `c` reads the `b_c`-adic digits `a_Q = (V div b_c^Q) mod b_c` of `V`
  (`V = ∑_Q a_Q b_c^Q`, `deg a_Q < e_c = deg b_c`), each written as the `e_c` base-`p` digits given by its
  coefficients, the coefficient of `z^{e_c-1}` first: `y_c(n) = ∑_Q ∑_{i<e_c} [z^{e_c-1-i}] a_Q p^{-(Q e_c+i+1)}`
  (finite: `a_Q = 0` for `Q > n`).
* *Distances.* `euclDist` is Euclidean; `torDist` is toroidal, `(∑_c ‖x_c - y_c‖²)^{1/2}` with
  `‖t‖ = |t - round t|`.
* *Quasi-uniformity* (`IsQuasiUniform`, as in Dick–Goda–Suzuki and Goda–Hofer–Suzuki): the mesh ratio
  `h(P_{[N]})/δ(P_{[N]})` of the first `N` points is bounded over all `N ≥ 2`; `h` is the covering radius
  over `[0,1]^s`, `δ` the minimum distance over pairs of distinct indices, both Euclidean.

**Two auxiliary theorems** make the statements checkably non-vacuous: `halton_bases_exist` (bases as in
`halton_not_quasiUniform` exist for every prime `p` and every `s`) and `residue_data` (`ρ ≥ 2`, so the
separation constant is positive; `v_c ≠ 0`; the places are distinct; and the two inverses in `resGen` are
genuine inverses, not the junk value `0⁻¹ = 0`). Neither quasi-uniformity statement is vacuous for a junk
reason either: the definition holds for the residue sequence and fails for every Halton-type sequence.

**Choices not visible in the paper's wording.** `div`/`mod` are Mathlib's polynomial division over the
field `𝔽_p` (unique quotient and remainder of degree `< deg b_c`, also for non-monic `b_c`). `N^{-1/s}`,
`p^{-1/s}` are `Real.rpow`, `ρ` is `Nat.floor` of `p^{1/s}`. The separation clause of the fix is toroidal
(it implies the Euclidean one); the close pairs of the fail are Euclidean (they bound the toroidal distance).
`δ` in `IsQuasiUniform` is Euclidean (DGS, GHS); the paper's `δ` (`sec:prelim`) is toroidal, hence no larger,
so the fail statement here is stronger than the paper's wording and the fix statement weaker.
-/

namespace GeoSeqV4

open Finset

-- BEGIN DEFINITIONS

/-- Base-`p` digit `v_k ∈ 𝔽_p` of the index `v = ∑_k v_k p^k`. -/
def idxDigit (p v k : ℕ) : ZMod p := ((v / p ^ k % p : ℕ) : ZMod p)

/-- Digit `n` of coordinate `c` of the point with index `v`: `y_{c,n}(v) = ∑_k C_c[n][k] v_k`
(a finite sum: `v_k = 0` for `k > v`). -/
def seqDigit {s : ℕ} (p : ℕ) (C : Fin s → ℕ → ℕ → ZMod p) (v : ℕ) (c : Fin s) (n : ℕ) : ZMod p :=
  ∑ k ∈ range (v + 1), C c n k * idxDigit p v k

/-- The point `y(v) ∈ [0,1]^s` of the digital sequence: `y_c(v) = ∑_{n ≥ 0} y_{c,n}(v) p^{-n-1}`. -/
noncomputable def seqPoint {s : ℕ} (p : ℕ) (C : Fin s → ℕ → ℕ → ZMod p) (v : ℕ) : Fin s → ℝ :=
  fun c => ∑' n : ℕ, ((seqDigit p C v c n).val : ℝ) / (p : ℝ) ^ (n + 1)

/-- The index `∑_{n<d} y_{c,n}(v) p^{d-1-n}` of the elementary interval of length `p^{-d}` that contains
coordinate `c` of `y(v)` (read off the first `d` digits). -/
def cellIdx {s : ℕ} (p : ℕ) (C : Fin s → ℕ → ℕ → ZMod p) (v : ℕ) (c : Fin s) (d : ℕ) : ℕ :=
  ∑ n : Fin d, (seqDigit p C v c n).val * p ^ (d - 1 - (n : ℕ))

/-- **`(0,s)`-sequence** in base `p`: for all `m, k`, every elementary box with `d_c` digits in coordinate
`c` (`∑_c d_c = m`, box index `a_c < p^{d_c}`) contains exactly one point `y(v)`, `k p^m ≤ v < (k+1) p^m`. -/
def IsSeq0 {s : ℕ} (p : ℕ) (C : Fin s → ℕ → ℕ → ZMod p) : Prop :=
  ∀ m k : ℕ, ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ a : Fin s → ℕ, (∀ c, a c < p ^ d c) →
    ∃! v : ℕ, (k * p ^ m ≤ v ∧ v < (k + 1) * p ^ m) ∧ ∀ c, cellIdx p C v c (d c) = a c

/-- The Euclidean distance `(∑_c (x_c - y_c)²)^{1/2}`. -/
noncomputable def euclDist {s : ℕ} (x y : Fin s → ℝ) : ℝ := Real.sqrt (∑ c, (x c - y c) ^ 2)

/-- The toroidal Euclidean distance `(∑_c ‖x_c - y_c‖²)^{1/2}`, `‖t‖ = |t - round t|`. -/
noncomputable def torDist {s : ℕ} (x y : Fin s → ℝ) : ℝ :=
  Real.sqrt (∑ c, (x c - y c - round (x c - y c)) ^ 2)

/-- The covering radius `h(P_{[N]}) = sup_{x ∈ [0,1]^s} min_{v < N} ‖x - y(v)‖` of the first `N` points. -/
noncomputable def covRad {s : ℕ} (pt : ℕ → Fin s → ℝ) (N : ℕ) : ℝ :=
  ⨆ x : {x : Fin s → ℝ // ∀ c, x c ∈ Set.Icc (0 : ℝ) 1}, ⨅ v : Fin N, euclDist x.1 (pt v)

/-- The minimum distance `δ(P_{[N]}) = min_{v ≠ w < N} ‖y(v) - y(w)‖` of the first `N` points. -/
noncomputable def sepDist {s : ℕ} (pt : ℕ → Fin s → ℝ) (N : ℕ) : ℝ :=
  ⨅ vw : {vw : Fin N × Fin N // vw.1 ≠ vw.2}, euclDist (pt vw.1.1) (pt vw.1.2)

/-- **Quasi-uniform**: the mesh ratio `h(P_{[N]})/δ(P_{[N]})` is bounded over all `N ≥ 2`. -/
def IsQuasiUniform {s : ℕ} (pt : ℕ → Fin s → ℝ) : Prop :=
  ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → covRad pt N ≤ B * sepDist pt N

/-- The index polynomial `V = ∑_k n_k z^k ∈ 𝔽_p[z]` of `n = ∑_k n_k p^k`. -/
noncomputable def idxPoly (p n : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ range (n + 1), Polynomial.monomial k (idxDigit p n k)

/-- The `Q`-th `b`-adic digit `a_Q = (V div b^Q) mod b` of `V = ∑_Q a_Q b^Q` (`deg a_Q < deg b`). -/
noncomputable def badicDigit {p : ℕ} [Fact p.Prime] (b V : Polynomial (ZMod p)) (Q : ℕ) :
    Polynomial (ZMod p) :=
  V / b ^ Q % b

/-- **The Halton-type sequence** in the bases `b_c` (GHS Def. 2): coordinate `c` of the point with index
`n` is `∑_Q ∑_{i<e_c} [z^{e_c-1-i}] a_Q · p^{-(Q e_c + i + 1)}`, `a_Q` the `b_c`-adic digits of `V(n)`. -/
noncomputable def haltonPt (p : ℕ) [Fact p.Prime] {s : ℕ} (b : Fin s → Polynomial (ZMod p)) (n : ℕ) :
    Fin s → ℝ :=
  fun c => ∑ Q ∈ range (n + 1), ∑ i ∈ range (b c).natDegree,
    (((badicDigit (b c) (idxPoly p n) Q).coeff ((b c).natDegree - 1 - i)).val : ℝ) /
      (p : ℝ) ^ (Q * (b c).natDegree + i + 1)

/-- The Faure places `a_c = c ∈ 𝔽_p`. -/
def place (p : ℕ) {s : ℕ} (c : Fin s) : ZMod p := ((c : ℕ) : ZMod p)

/-- `w_c(z) = ∏_{c' ≠ c} (z - a_{c'})`, so that `w = (z - a_c) w_c` with `w = ∏_c (z - a_c)`. -/
noncomputable def wPart (p : ℕ) {s : ℕ} (c : Fin s) : Polynomial (ZMod p) :=
  ∏ c' ∈ univ.erase c, (Polynomial.X - Polynomial.C (place p c'))

/-- The Korobov check vector `v = (ρ, ρ², …, ρ^{s-1}, -1)`, `ρ = ⌊p^{1/s}⌋`. -/
noncomputable def korobov (p s : ℕ) (c : Fin s) : ZMod p :=
  if (c : ℕ) + 1 < s then ((⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ ^ ((c : ℕ) + 1) : ℕ) : ZMod p) else -1

/-- **The residue sequence** `𝓡_v` (`def:residue`, Faure places, scale `θ = 1`):
`C_c[n][i] = v_c^{-1} [(z - a_c)^n] z^i / w_c(z)^{n+1}`, the coefficient of `t^n` in the power series
`(a_c + t)^i · w_c(a_c + t)^{-(n+1)} ∈ 𝔽_p[[t]]` (`Polynomial.taylor a f = f(z + a)`). -/
noncomputable def resGen (p : ℕ) [Fact p.Prime] {s : ℕ} (v : Fin s → ZMod p) :
    Fin s → ℕ → ℕ → ZMod p :=
  fun c n i => (v c)⁻¹ * PowerSeries.coeff n
    ((Polynomial.taylor (place p c) (Polynomial.X ^ i) : PowerSeries (ZMod p)) *
      ((Polynomial.taylor (place p c) (wPart p c) : PowerSeries (ZMod p))⁻¹) ^ (n + 1))

-- END DEFINITIONS

/-- **`cor:halton`** (Goda–Hofer–Suzuki, Open Problem 2). For every prime `p`, every `s ≥ 2` and all pairwise
coprime `b_0, …, b_{s-1} ∈ 𝔽_p[z]` of degrees `≥ 1`, the Halton-type sequence in these bases has, for every
`ε > 0`, a prefix of `p^m` points containing two points at Euclidean distance `< ε p^{-m/s}`; and it is not
quasi-uniform. -/
theorem halton_not_quasiUniform (p : ℕ) [Fact p.Prime] (s : ℕ) (hs : 2 ≤ s)
    (b : Fin s → Polynomial (ZMod p)) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (haltonPt p b v) (haltonPt p b w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (haltonPt p b) := by
  sorry

/-- **Non-vacuity of `halton_not_quasiUniform`.** For every prime `p` and every `s` there are pairwise
coprime `b_0, …, b_{s-1} ∈ 𝔽_p[z]` of degrees `≥ 1` (e.g. Euclid's `b_0 = z`, `b_{c+1} = z b_0 ⋯ b_c + 1`). -/
theorem halton_bases_exist (p : ℕ) [Fact p.Prime] (s : ℕ) :
    ∃ b : Fin s → Polynomial (ZMod p),
      (∀ c, 1 ≤ (b c).natDegree) ∧ Pairwise fun c c' => IsCoprime (b c) (b c') := by
  sorry

/-- **`thm:residue` with `cor:korobov` and `cor:residueQU`.** For every `s ≥ 2` and every prime
`p > 2^s` the residue sequence `𝓡_v` with the Korobov check vector is a digital `(0,s)`-sequence over `𝔽_p`;
for every `K ≥ 1` any two distinct points among its first `N = p^{sK-1}` points have toroidal distance
`≥ (⌊p^{1/s}⌋ - 1) p^{-1/s} N^{-1/s}`; and it is quasi-uniform. -/
theorem residue_quasiUniform (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    IsSeq0 p (resGen p (korobov p s)) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ v w : ℕ, v < p ^ (s * K - 1) → w < p ^ (s * K - 1) → v ≠ w →
        ((⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) *
            ((p ^ (s * K - 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / s) ≤
          torDist (seqPoint p (resGen p (korobov p s)) v) (seqPoint p (resGen p (korobov p s)) w)) ∧
      IsQuasiUniform (seqPoint p (resGen p (korobov p s))) := by
  sorry

/-- **The data of `residue_quasiUniform` are the paper's** (`def:residue`, `cor:korobov`). For `s ≥ 2` and
prime `p > 2^s`: `ρ = ⌊p^{1/s}⌋ ≥ 2` and `ρ^s < p`, so the separation constant `(ρ - 1) p^{-1/s}` is positive;
the Korobov vector is a check vector (`v_c ≠ 0`, so `v_c^{-1}` in `resGen` is a genuine inverse); the Faure
places are distinct; and the power series `w_c(a_c + t)` (constant term `w_c(a_c) ≠ 0`) has a genuine inverse
in `𝔽_p[[t]]`. -/
theorem residue_data (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    2 ≤ ⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ ∧ ⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ ^ s < p ∧
      (∀ c, korobov p s c ≠ 0) ∧ Function.Injective (place p : Fin s → ZMod p) ∧
      ∀ c : Fin s, (Polynomial.taylor (place p c) (wPart p c) : PowerSeries (ZMod p)) *
        (Polynomial.taylor (place p c) (wPart p c) : PowerSeries (ZMod p))⁻¹ = 1 := by
  sorry

end GeoSeqV4
