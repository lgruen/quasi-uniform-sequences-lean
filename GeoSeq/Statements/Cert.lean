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
# Statements: the certificate `lem:cert` in its point-set form (`sec:law`), GeoSeq stage S2

Compared theorems (statement with `sorry`; proofs in `GeoSeq/Cert.lean`, restated by name).

* `nat_carry`, `carry_digits`: the carry of a cell index (`rem:F4carry`; torus wrap included).
* `coord_split`: `q^K y_c = n_c + enc(R_c)/q^j + ε_c`, `0 ≤ ε_c ≤ q^{-j}` (`eq:cellunits`, the jitter is
  the infinite digit tail).
* `tor_far`, `tor_near`, `gap_bound`: toroidal distance in cell units and the coordinatewise gap `f_j`.
* `law_step`: linearity of the level law (carry responses, `IsCarryEntry`).
* `digInc_zcode`: for `ℤ/qℤ` every step adds `1` (`Δ ≡ 1`).
* **`cert`** (general digit code with the carry change `δ_i(l, y)` of `eq:carrychange`),
  **`cert_prime`** (`ℤ/qℤ`, `δ_i(l, y) = D_i(l)`), **`cert_one`** (`j = 1` with `f_1 = gapNum1/q`).

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset

/-- A carry in base `q`: the digits (position `t`, least significant first) of `A < q^K` and of
`B = (A+1) mod q^K` agree above a position `L < K`, `B_L = (A_L + 1) mod q`, and below `L` the digits
of `A` are `q-1` and those of `B` are `0`. -/
theorem nat_carry {q : ℕ} (hq : 2 ≤ q) (K : ℕ) (hK : 1 ≤ K) :
    ∀ A, A < q ^ K → ∃ L < K,
      (∀ t < L, A / q ^ t % q = q - 1 ∧ (A + 1) % q ^ K / q ^ t % q = 0) ∧
      (A + 1) % q ^ K / q ^ L % q = (A / q ^ L % q + 1) % q ∧
      ∀ t, L < t → t < K → (A + 1) % q ^ K / q ^ t % q = A / q ^ t % q := by
  sorry

section Digits

variable {R : Type*} [CommRing R] {q : ℕ} [NeZero q]

/-- **The carry of a cell index** (`rem:F4carry`): if the cell index with digits `z` (most
significant first) is the successor modulo `q^K` of the one with digits `x`, there is a carry length
`l ∈ [1, K]` such that the digits change by `Δ(ȳ)` on the `l - 1` finest digits, by `Δ(x_{K-l})` at
digit `K - l`, and not at all above (the torus wrap is `l = K`). -/
theorem carry_digits (D : DigitCode R q) (hq : 2 ≤ q) (K : ℕ) (hK : 1 ≤ K) (x z : ℕ → R)
    (hcell : ∑ n : Fin K, (D.enc (z n) : ℕ) * q ^ (K - 1 - (n : ℕ)) =
      (∑ n : Fin K, (D.enc (x n) : ℕ) * q ^ (K - 1 - (n : ℕ)) + 1) % q ^ K) :
    ∃ l, 1 ≤ l ∧ l ≤ K ∧ ∀ n < K, z n - x n =
      digInc D (topDigit D) * (if K - (l - 1) ≤ n then 1 else 0) +
        digInc D (x (K - l)) * (if n = K - l then 1 else 0) := by
  sorry

end Digits

/-- **`eq:cellunits`**: for digits `a_n < q`, `q^K ∑_n a_n q^{-n-1} = n + enc(R)/q^j + ε` with
`n = ∑_{n<K} a_n q^{K-1-n}` (the cell), `enc(R) = ∑_{i<j} a_{K+i} q^{j-1-i}` (the `j` geometric
digits) and the jitter `0 ≤ ε ≤ q^{-j}` (the tail `∑_{n ≥ K+j} a_n q^{K-n-1}`). -/
theorem coord_split {q : ℕ} (hq : 2 ≤ q) (a : ℕ → ℕ) (ha : ∀ n, a n < q) (K j : ℕ) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / (q : ℝ) ^ j ∧
      (q : ℝ) ^ K * ∑' n, (a n : ℝ) / (q : ℝ) ^ (n + 1) =
        ((∑ n : Fin K, a n * q ^ (K - 1 - (n : ℕ)) : ℕ) : ℝ) +
          ((∑ i : Fin j, a (K + i) * q ^ (j - 1 - (i : ℕ)) : ℕ) : ℝ) / (q : ℝ) ^ j + ε := by
  sorry

/-- Cells at least two apart on the torus (`2 ≤ |b - a| ≤ Q - 2`) give a coordinate gap `≥ 1` cell. -/
theorem tor_far {Q y y' a b u u' : ℝ} (hQ : 0 < Q) (hya : Q * y = a + u) (hyb : Q * y' = b + u')
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hu0' : 0 ≤ u') (hu1' : u' ≤ 1)
    (h2 : 2 ≤ |b - a|) (hQ2 : |b - a| ≤ Q - 2) :
    1 ≤ Q * Z3NetDGS.torCoord y y' := by
  sorry

/-- Neighbouring cells (`b - a ≡ e (mod Q)`, `e ∈ {-1,0,1}`), `Q ≥ 4`: the coordinate gap in cell
units is at least `|e + u' - u|` (the difference is at most `2 ≤ Q/2`, so it is the toroidal one). -/
theorem tor_near {Q y y' a b u u' e : ℝ} (hQ : 4 ≤ Q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hy0' : 0 ≤ y')
    (hy1' : y' ≤ 1) (hya : Q * y = a + u) (hyb : Q * y' = b + u')
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hu0' : 0 ≤ u') (hu1' : u' ≤ 1) (he : |e| ≤ 1)
    (hk : b - a - e = 0 ∨ b - a - e = Q ∨ b - a - e = -Q) :
    |e + u' - u| ≤ Q * Z3NetDGS.torCoord y y' := by
  sorry

/-- The coordinatewise relaxation: with `u = E/Q_j + ε`, `u' = E'/Q_j + ε'`, jitters in `[0, 1/Q_j]`
and `N ≤ |e Q_j + E' - E|`, the gap is at least `(N - 1)/Q_j` (`f_j` of `lem:cert`). -/
theorem gap_bound {Qj : ℝ} (hQj : 0 < Qj) (e E E' ε ε' : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / Qj)
    (hε0' : 0 ≤ ε') (hε1' : ε' ≤ 1 / Qj) (N : ℕ) (hN : (N : ℝ) ≤ |e * Qj + E' - E|) :
    ((N - 1 : ℕ) : ℝ) / Qj ≤ |e + (E' / Qj + ε') - (E / Qj + ε)| := by
  sorry

section Law

variable {R : Type*} [CommRing R] {s : ℕ}

/-- **The step of the level law** (linearity, `sec:law`): if the cell digits of an index vector `Vd`
are the combination `∑_{c'} (a_{c'} carryPat(l_{c'}-1) + b_{c'} (carryPat(l_{c'}) - carryPat(l_{c'}-1)))`
of carry patterns, its geometric digit `K+i` of coordinate `c` is the same combination of the carry
responses `D_i(l)` (`IsCarryEntry`; `D_i(0) = 0`). -/
theorem law_step (C : Gen s R) (K j : ℕ) (hK1 : 1 ≤ K) (Dr : ℕ → ℕ → Fin s → Fin s → R)
    (hD0 : ∀ i c c', Dr i 0 c c' = 0)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (i : ℕ) (hi : i < j) (c : Fin s) (Vd : Fin (s * K) → R) (a b : Fin s → R) (l : Fin s → ℕ)
    (hl : ∀ c, 1 ≤ l c ∧ l c ≤ K)
    (hcellD : ∀ c₁, ∀ n < K, vecDigit C Vd c₁ n = ∑ c', (a c' * carryPat K (l c' - 1) c' c₁ n +
      b c' * (carryPat K (l c') c' c₁ n - carryPat K (l c' - 1) c' c₁ n))) :
    vecDigit C Vd c (K + i) =
      ∑ c', (a c' * Dr i (l c' - 1) c c' + b c' * (Dr i (l c') c c' - Dr i (l c' - 1) c c')) := by
  sorry

end Law

section Main

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **`lem:cert`** (certificate, general digit code; `δ_i(l, y)` of `eq:carrychange`). Let the prefix
`P_{sK}` be a `(0, sK, s)`-net in base `q` with `q^K ≥ 4`, let `Dr i l = D_i(l)` be its carry responses
for `i < j`, `1 ≤ l ≤ K` (`IsCarryEntry`, with `D_i(0) = 0`), and let `LB` be at most every certificate
term `(∑_c f_j(e_c, σ_c)²)^{1/2}` over all steps `e ∈ {-1,0,1}^s \ {0}`, carry lengths `l_c ∈ [1, K]` and
stop digits `y_c` (`σ_c = certSigma`). Then `c(P_{sK}) ≥ min(1, LB)`: any two distinct points of
`P_{sK}` have toroidal distance at least `min(1, LB) · q^{-K}`. -/
theorem cert [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (K j : ℕ)
    (hK : 4 ≤ q ^ K) (hnet : BlockNet0 D C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → R)
    (hD0 : ∀ i c c', Dr i 0 c c' = 0)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ)
    (hLB : ∀ e l, IsStep K e l → ∀ y : Fin s → R, LB ≤ certTerm D j e (certSigma D Dr j e l y)) :
    SepAtLevel q s K (seqPoint D C) (min 1 LB) := by
  sorry

/-- For `ℤ/qℤ` with `enc = val`, every step adds `1` to the digits it changes: `Δ ≡ 1`. -/
theorem digInc_zcode (q : ℕ) [NeZero q] (y : ZMod q) : digInc (zcode q) y = 1 := by
  sorry

/-- **`lem:cert`, prime `q`** (`ℤ/qℤ`, `enc = val`; the statement holds for every `q`, the paper uses
it for prime `q = p`, where `ℤ/pℤ = 𝔽_p`): with the carry responses `Dr i l = D_i(l)`
(`i < j`, `1 ≤ l ≤ K`) of a `(0, sK, s)`-net `P_{sK}`, `q^K ≥ 4`, and `LB` at most every term
`(∑_c f_j(e_c, σ_c)²)^{1/2}`, `σ_{c,i} = ∑_{c'} e_{c'} D_i(l_{c'})[c][c']`, over all steps `e` and carry
lengths `l_c ∈ [1, K]`: `c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_prime {q s : ℕ} [NeZero q] (C : Gen s (ZMod q)) (K j : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l → LB ≤ certTerm (zcode q) j e (certSigmaP Dr j e l)) :
    SepAtLevel q s K (seqPoint (zcode q) C) (min 1 LB) := by
  sorry

/-- **`lem:cert` with one geometric digit** (`j = 1`, `ℤ/qℤ`; the form used by `thm:WF` and the earlier
version's `thm:GA`, `lem:dom` together with `rem:onedigit`): with the one-digit responses `Dr l = D(l)` (`1 ≤ l ≤ K`) and
`LB` at most every `(∑_c f_1(e_c, σ_c)²)^{1/2}`, `σ_c = ∑_{c'} e_{c'} D(l_{c'})[c][c']`,
`c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_one {q s : ℕ} [NeZero q] (C : Gen s (ZMod q)) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 q (e c) (∑ c', (e c' : ZMod q) * Dr (l c') c c') : ℝ) / q) ^ 2)) :
    SepAtLevel q s K (seqPoint (zcode q) C) (min 1 LB) := by
  sorry

end Main

end GeoSeq
