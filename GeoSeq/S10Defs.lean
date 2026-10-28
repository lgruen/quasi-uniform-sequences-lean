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
# GeoSeq stage S10: definitions for the structural results (`sec:LI`, `sec:limits`, `app:dual`)

* `LawFinest C K c c'`: the one-digit law entry `(c, c')` is *finest-digit* at level `K`
  (`sec:LI`, before `prop:N1`): the partial sums `D(l)[c][c']`, `1 ≤ l ≤ K`, do not depend on `l`.
* `IsRatPS f`: the power series `f` is rational (`Q f = P` for polynomials `P`, `Q ≠ 0`), and
  `EvPeriodic a`: the sequence `a` is eventually periodic (`prop:N2`).
* `crossFin`: the finest `(s-1)`-minor matrix of the cross rows (`prop:rank2`).
* `kumU`-type directions of the twisted symmetric Kummer families (`prop:composite`): `twU`.
* `dualGen`: the dual-number Faure matrices `eq:dual` (`thm:dual`).
-/

namespace GeoSeq

open Finset PowerSeries

variable {R : Type*} [CommRing R] {s : ℕ}

/-- **Finest-digit law** (`sec:LI`): at level `K` the one-digit carry responses `D(l)[c][c']`,
`1 ≤ l ≤ K`, are all equal (equivalently, the law coefficients of entry `(c, c')` vanish at all carry
depths beyond the first one). For `c ≠ c'` this is a finest-digit cross law, for `c = c'` a
finest-digit own law. -/
def LawFinest (C : Gen s R) (K : ℕ) (c c' : Fin s) : Prop :=
  ∃ d : R, ∀ l, 1 ≤ l → l ≤ K → IsCarryEntry C K 0 l c c' d

/-- A power series is **rational** if `Q · f = P` for polynomials `P`, `Q` with `Q ≠ 0`. -/
def IsRatPS {F : Type*} [CommRing F] (f : PowerSeries F) : Prop :=
  ∃ P Q : Polynomial F, Q ≠ 0 ∧ (Q : PowerSeries F) * f = (P : PowerSeries F)

/-- A sequence is **eventually periodic**: `a (n + T) = a n` for all `n ≥ N`, some `T ≥ 1`. -/
def EvPeriodic {α : Type*} (a : ℕ → α) : Prop :=
  ∃ N T : ℕ, 1 ≤ T ∧ ∀ n, N ≤ n → a (n + T) = a n

/-- The finest `(s-1)`-minor matrix of the cross rows of column `c'` (`prop:rank2`), for `s = n + 1`:
entry `(i, j)` is the coefficient `coef (c'.succAbove i) c' (K - n + j)` of the cell digit
`y_{c', K-n+j}` in the geometric digit `r_{c'.succAbove i}` (rows: the coordinates `c ≠ c'`). -/
def crossFin {n : ℕ} (coef : Fin (n + 1) → Fin (n + 1) → ℕ → R) (K : ℕ) (c' : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => coef (c'.succAbove i) c' (K - n + (j : ℕ))

/-- `w'(a_{c'}) = ∏_{c ≠ c'} (a_{c'} - a_c)` for a frame with places `a = ssPlace zθ` (`prop:LI`). -/
noncomputable def placeDer {F : Type*} [Field F] {s : ℕ} (zθ : Fin s → PowerSeries F) (c' : Fin s) : F :=
  ∏ c ∈ univ.erase c', (ssPlace zθ c' - ssPlace zθ c)

/-- **The free series of column `c'`** (`prop:LI`(a), with `ϖ = dz`), as a series in `x`:
`ψ_{c'}(θx) = g_{c'}(0) w'(a_{c'}) / (g_{c'}(x) w'(z_{c'}(θx)))`, where
`w'(z_{c'}(θx)) = ∏_{c ≠ c'} (z_{c'}(θx) - z_c(θx))` (the roots of `w(Z) - θx` are the `z_c(θx)`). -/
noncomputable def freeSer {F : Type*} [Field F] {s : ℕ} (g zθ : Fin s → PowerSeries F) (c' : Fin s) :
    PowerSeries F :=
  C (constantCoeff (g c') * placeDer zθ c') *
    (g c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹

/-- `κ_{c←c'} = θ g_c(0) / (g_{c'}(0) w'(a_{c'}) (a_{c'} - a_c))` (`prop:LI`(c)). -/
noncomputable def kap {F : Type*} [Field F] {s : ℕ} (θ : F) (g zθ : Fin s → PowerSeries F) (c c' : Fin s) :
    F :=
  θ * constantCoeff (g c) /
    (constantCoeff (g c') * placeDer zθ c' * (ssPlace zθ c' - ssPlace zθ c))

/-- The cross directions of the twisted symmetric Kummer family (`sec:limits`, `prop:composite`):
`u_d = θ ϱ^d / (s (1 - ζ^d))`. -/
def twU {F : Type*} [Field F] (s : ℕ) (θ ϱ ζ : F) (d : ℕ) : F :=
  θ * ϱ ^ d / ((s : F) * (1 - ζ ^ d))

/-- **`eq:dual`**: the dual-number Faure matrices `C_c = P_{a_c} ⊗ B(ξ_c)`,
`C_c[2k'+i][2k+j] = binom(k, k') a_c^{k-k'} B(ξ_c)[i][j]`, `B(ξ) = ((1, ξ), (0, 1))`. -/
def dualGen {F : Type*} [Field F] {s : ℕ} (a ξ : Fin s → F) : Gen s F :=
  fun c n k => pas (a c) (n / 2) (k / 2) *
    (if n % 2 = k % 2 then 1 else if n % 2 = 0 ∧ k % 2 = 1 then ξ c else 0)

/-- The symmetric law of `lem:H` as a carry-response table (`j = 1`): `D(l)[c][c] = O^{(l)}`,
`D(l)[c][c'] = X^{(l)}` (`c ≠ c'`). -/
def symLaw {p : ℕ} (Ol Xl : ℕ → ZMod p) : ℕ → ℕ → Fin 2 → Fin 2 → ZMod p :=
  fun _ l c c' => if c = c' then Ol l else Xl l

end GeoSeq
