/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# GeoSeq stage V9 (paper V4): definitions for residues and residue sequences

Shared by the statement file `GeoSeq/Statements/V9.lean` and the proof files `GeoSeq/V9*.lean`.

* **Local residues without Laurent series** (`lem:resform`). For a polynomial `U` with `U(a) ≠ 0`,
  `Res_a(V / ((z - a)^k U) dz)` is the coefficient of `t^{k-1}` in the power series
  `V(a + t) · U(a + t)^{-1}` (`locRes`; `Polynomial.taylor a f = f(z + a)`). Every rational function
  with poles only at the places `a_c` and `∞` is `F = V / ∏_c (z - a_c)^{k_c}` (`placePoly`); its residue
  at `a_c` is `resAt` (the cofactor `placeCo a k c = ∏_{c' ≠ c} (z - a_{c'})^{k_{c'}}` is a unit at `a_c`),
  and its coefficient `[z^{-1}] F` at `∞` is `resInf`: dividing, `V = Q D + R` with `deg R < deg D = M`
  and `D` monic, so `F = Q + R/D` and `[z^{-1}] F = [z^{M-1}] R` (the polynomial `Q` has no `z^{-1}`
  term, and `R/D = [z^{M-1}]R · z^{-1} + O(z^{-2})`).
* **Residue sequences** (`def:residue`). `w = ∏_c (z - a_c)` (`wPoly`), `w_c = ∏_{c' ≠ c}(z - a_{c'})`
  (`wCo`); the scramble `resL` (`L_c[n][k] = v_c^{-1} θ^{n+1} [t^{n-k}] w_c(a_c + t)^{-(n+1)}`, used for
  `k ≤ n`), and the generator matrices `resSeq = scrGen a resL`, i.e. `C_c = L_c P_{a_c}`
  (`resSeq_apply` gives the paper's entry formula `C_c[n][i] = v_c^{-1} θ^{n+1} [(z-a_c)^n] z^i/w_c^{n+1}`).
* **The lattice and its jitter length** (`thm:residue`): `Λ_v = {b ∈ ℤ^s : ∑_c v_c b_c ≡ 0 (mod p)}`
  (`InLat`), `‖(|b| - 1)_+‖_2` (`jitNorm`), `ℓ_jit(Λ_v)` (`ljit`, an infimum over the nonzero lattice
  vectors), and the Korobov check vector `(ρ, ρ², …, ρ^{s-1}, -1)`, `ρ = ⌊p^{1/s}⌋` (`korobov`).
* **Level families** (`lem:prefix`): the separation of a prefix `P_m` (`SepAtPrefix`, the statement
  `sep(P_m) ≥ LB`), and the largest-gap condition `Δ_Λ ≤ Δ` (`HasGap`).
* **Polar differentials** (`lem:resform`(a)): the numerator `polarNum` of `∑_{k ≤ n} l_k (z - a)^{-k-1} dz`.
* **Index forms** (the definitions of the Palomar statement): the toroidal distance with `round`
  (`torDistR`), the covering radius and minimum distance with minima over indices (`covRadIdx`, `sepDistIdx`),
  and quasi-uniformity (`IsQuasiUniform`, bounded mesh ratio over all `N ≥ 2`).
-/

namespace GeoSeq

open Finset Polynomial

section Res
variable {F : Type*} [Field F] {s : ℕ}

/-- `Res_a(V / ((z - a)^k U) dz)` for a polynomial `U` with `U(a) ≠ 0`: the coefficient of `t^{k-1}` in
`V(a + t) · U(a + t)^{-1} ∈ F[[t]]` (`0` for `k = 0`, when the function is regular at `a`). -/
noncomputable def locRes (a : F) (k : ℕ) (V U : F[X]) : F :=
  if k = 0 then 0 else
    PowerSeries.coeff (k - 1) ((taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹)

/-- The denominator `∏_c (z - a_c)^{k_c}` of a rational function with poles only at the places. -/
noncomputable def placePoly (a : Fin s → F) (k : Fin s → ℕ) : F[X] := ∏ c, (X - C (a c)) ^ k c

/-- The cofactor `∏_{c' ≠ c} (z - a_{c'})^{k_{c'}}` of `(z - a_c)^{k_c}` in `placePoly a k`. -/
noncomputable def placeCo (a : Fin s → F) (k : Fin s → ℕ) (c : Fin s) : F[X] :=
  ∏ c' ∈ univ.erase c, (X - C (a c')) ^ k c'

/-- `Res_{a_c}(F dz)` for `F = V / ∏_{c'} (z - a_{c'})^{k_{c'}}`. -/
noncomputable def resAt (a : Fin s → F) (k : Fin s → ℕ) (V : F[X]) (c : Fin s) : F :=
  locRes (a c) (k c) V (placeCo a k c)

/-- `[z^{-1}] F` at `∞` for `F = V / D`, `D = ∏_c (z - a_c)^{k_c}` monic of degree `M = ∑_c k_c`:
the coefficient of `z^{M-1}` in the remainder `V mod D`. -/
noncomputable def resInf (a : Fin s → F) (k : Fin s → ℕ) (V : F[X]) : F :=
  (V %ₘ placePoly a k).coeff (∑ c, k c - 1)

/-- The index polynomial `∑_{j<m} f_j z^j` of the digit vector `(f_0, …, f_{m-1})`. -/
noncomputable def vecPoly (f : ℕ → F) (m : ℕ) : F[X] := ∑ j ∈ range m, C (f j) * X ^ j

/-- The numerator `P(z) = ∑_{k ≤ n} l_k (z - a)^{n-k}` of the polar differential
`η = ∑_{k ≤ n} l_k (z - a)^{-k-1} dz = P(z) (z - a)^{-n-1} dz` (`lem:resform`(a)). -/
noncomputable def polarNum (a : F) (l : ℕ → F) (n : ℕ) : F[X] :=
  ∑ k ∈ range (n + 1), C (l k) * (X - C a) ^ (n - k)

/-- `w = ∏_c (z - a_c)`. -/
noncomputable def wPoly (a : Fin s → F) : F[X] := ∏ c, (X - C (a c))

/-- `w_c = ∏_{c' ≠ c} (z - a_{c'})`, so that `w = (z - a_c) w_c`. -/
noncomputable def wCo (a : Fin s → F) (c : Fin s) : F[X] := ∏ c' ∈ univ.erase c, (X - C (a c'))

/-- The scramble of the residue sequence (`lem:residue-t0`):
`L_c[n][k] = v_c^{-1} θ^{n+1} [t^{n-k}] w_c(a_c + t)^{-(n+1)}` (only `k ≤ n` is used by `scrGen`). -/
noncomputable def resL (a : Fin s → F) (θ : F) (v : Fin s → F) : Fin s → ℕ → ℕ → F :=
  fun c n k => (v c)⁻¹ * θ ^ (n + 1) *
    PowerSeries.coeff (n - k) (((taylor (a c) (wCo a c) : PowerSeries F)⁻¹) ^ (n + 1))

/-- **The residue sequence** `𝓡_v` (`def:residue`) with places `a`, scale `θ` and check vector `v`:
`C_c = L_c P_{a_c}` with `L_c = resL`; digit `n` of coordinate `c` is
`y_{c,n}(V) = v_c^{-1} Res_{a_c}(V (θ/w)^{n+1} dz)` (`resSeq_digit`). -/
noncomputable def resSeq (a : Fin s → F) (θ : F) (v : Fin s → F) : Gen s F := scrGen a (resL a θ v)

end Res

section Lattice
variable {s : ℕ}

/-- `b ∈ Λ_v`: `∑_c v_c b_c ≡ 0 (mod p)` (`thm:residue`; the Construction-A lattice of the check vector). -/
def InLat {p : ℕ} (v : Fin s → ZMod p) (b : Fin s → ℤ) : Prop := ∑ c, v c * (b c : ZMod p) = 0

/-- `‖(|b| - 𝟏)_+‖_2`, one unit of jitter subtracted in every coordinate. -/
noncomputable def jitNorm (b : Fin s → ℤ) : ℝ := Real.sqrt (∑ c, (max (|(b c : ℝ)| - 1) 0) ^ 2)

/-- `ℓ_jit(Λ_v) = min_{0 ≠ b ∈ Λ_v} ‖(|b| - 𝟏)_+‖_2`, as an infimum (the set is nonempty, `p e_0 ∈ Λ_v`,
and bounded below by `0`). -/
noncomputable def ljit {p : ℕ} (v : Fin s → ZMod p) : ℝ :=
  ⨅ b : {b : Fin s → ℤ // b ≠ 0 ∧ InLat v b}, jitNorm b.1

/-- `ρ = ⌊p^{1/s}⌋` (`cor:korobov`). -/
noncomputable def korRho (p s : ℕ) : ℕ := ⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊

/-- The Korobov check vector `v = (ρ, ρ², …, ρ^{s-1}, -1)`, `ρ = ⌊p^{1/s}⌋` (`cor:korobov`). -/
noncomputable def korobov (p s : ℕ) (c : Fin s) : ZMod p :=
  if (c : ℕ) + 1 < s then ((⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ ^ ((c : ℕ) + 1) : ℕ) : ZMod p) else -1

/-- The Faure places `a_c = c ∈ ℤ/pℤ`. -/
def faurePlace (p : ℕ) {s : ℕ} (c : Fin s) : ZMod p := ((c : ℕ) : ZMod p)

/-- `sep(P_m) ≥ LB`: any two distinct points of the prefix `P_m = {y(v) : v < q^m}` have toroidal
Euclidean distance `≥ LB · (q^m)^{-1/s} = LB · N^{-1/s}` (`N = q^m`; `sec:prelim`). -/
def SepAtPrefix (q s m : ℕ) (pt : ℕ → Fin s → ℝ) (LB : ℝ) : Prop :=
  ∀ v w : ℕ, v < q ^ m → w < q ^ m → v ≠ w →
    LB * ((q : ℝ) ^ m) ^ (-(1 / (s : ℝ))) ≤ Z3NetDGS.torDist2 (pt v) (pt w)

/-- The level family `Lev` (a set of exponents `m ≥ 1`) has largest gap `Δ_Lev ≤ Δ` (`lem:prefix`):
every `m ≥ 0` has an element `m'` of the family with `m < m' ≤ m + Δ`. (With `m = 0` this is
`min Lev ≤ Δ`; with `m` an element of the family it bounds the gap to the next element; conversely
both bounds give this condition.) -/
def HasGap (Lev : ℕ → Prop) (Δ : ℕ) : Prop := ∀ m : ℕ, ∃ m', Lev m' ∧ m < m' ∧ m' ≤ m + Δ

/-- The toroidal Euclidean distance written with `round`: `(∑_c ‖x_c - y_c‖²)^{1/2}`, `‖t‖ = |t - round t|`
(the form of the Palomar statement; equal to `Z3NetDGS.torDist2` on `[0,1]^s`, `torDistR_eq`). -/
noncomputable def torDistR (x y : Fin s → ℝ) : ℝ :=
  Real.sqrt (∑ c, (x c - y c - round (x c - y c)) ^ 2)

/-- The covering radius `h(P_{[N]}) = sup_{x ∈ [0,1]^s} min_{v < N} ‖x - y(v)‖` of the first `N` points, with
the minimum over indices (the form of the Palomar statement). -/
noncomputable def covRadIdx (pt : ℕ → Fin s → ℝ) (N : ℕ) : ℝ :=
  ⨆ x : {x : Fin s → ℝ // ∀ c, x c ∈ Set.Icc (0 : ℝ) 1}, ⨅ v : Fin N, euclDist x.1 (pt v)

/-- The minimum distance `δ(P_{[N]}) = min_{v ≠ w < N} ‖y(v) - y(w)‖` over pairs of distinct indices
(Euclidean; the form of the Palomar statement). -/
noncomputable def sepDistIdx (pt : ℕ → Fin s → ℝ) (N : ℕ) : ℝ :=
  ⨅ vw : {vw : Fin N × Fin N // vw.1 ≠ vw.2}, euclDist (pt vw.1.1) (pt vw.1.2)

/-- **Quasi-uniform** (`sec:prelim`, Dick–Goda–Suzuki): the mesh ratio `h(P_{[N]})/δ(P_{[N]})` is bounded over
all `N ≥ 2` (`h`, `δ` Euclidean, `δ` over distinct indices). -/
def IsQuasiUniform (pt : ℕ → Fin s → ℝ) : Prop :=
  ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → covRadIdx pt N ≤ B * sepDistIdx pt N

end Lattice

end GeoSeq
