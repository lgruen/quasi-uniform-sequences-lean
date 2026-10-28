/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S11: definitions for Appendix C (`app:machinery`)

The Faure frame `(0, 1; ∞)`, `w = z(z-1)`, over a field `F`. All objects are written without
residues: a differential `h(t) t^{-j-1} dt` with a pole at a place is represented by the linear
functional `V ↦ Res(V · h t^{-j-1} dt) = [t^j] (V h)` on polynomials `V` (the index polynomials),
`t` the local coordinate at the place.

* `faurePl = (0, 1)`, `faureDel c = a_c - a_{1-c} = (-1, 1)`.
* `scrDig a L n V = y_{c,n}(V) = ∑_{i ≤ n} L[n][i] [(z-a)^i] V`: the digits of an arbitrary scramble
  `C_c = L_c P_{a_c}` (`scrGen`) as functionals of the index polynomial `V` (rows as differentials,
  `η_{c,n} = ∑_k L_c[n][k] (z-a_c)^{-k-1} dz`).
* `ebas c j V = Res_{a_c}(V e_{c,j})` with the e-basis `e_{c,j} = w^{-j-1} ϖ_c`, `ϖ_c = dz/(z - a_{1-c})`;
  in the coordinate `t = z - a_c`: `w = t (t + δ_c)`, `e_{c,j} = t^{-j-1} (t + δ_c)^{-j-2} dt`.
* `tRoot`: the series `T(w)` with `T + T² = w`, `T(0) = 0` (compositional inverse of `t + t²`); the local
  roots of `z² - z = w` are `zF 0 = -T` (at `0`) and `zF 1 = 1 + T` (at `1`), and `gamF = γ(w) = z_1(w)²`.
* `LevelInv C` (`def:LI`): the one-digit carry responses `D(l)[c][c']` do not depend on the level.
* `convL ω`: the characteristic-two counterexample of `rem:convchar2` (instance `X = X' = 1`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

/-- The Faure places `a_0 = 0`, `a_1 = 1`. -/
def faurePl : Fin 2 → F := ![0, 1]

/-- `δ_c = a_c - a_{1-c}`: `δ_0 = -1`, `δ_1 = 1` (`w = t (t + δ_c)` in the coordinate `t = z - a_c`). -/
def faureDel : Fin 2 → F := ![-1, 1]

/-- **Digits of an arbitrary scramble** as functionals of the index polynomial `V`:
`y_{c,n}(V) = ∑_{i ≤ n} L[n][i] [(z-a)^i] V` (`app:machinery`, rows as differentials). -/
noncomputable def scrDig (a : F) (L : ℕ → ℕ → F) (n : ℕ) (V : F[X]) : F :=
  ∑ i ∈ range (n + 1), L n i * (Polynomial.taylor a V).coeff i

/-- **The e-basis functionals** (`app:machinery`): `ebas c j V = Res_{a_c}(V w^{-j-1} ϖ_c)`, with
`ϖ_c = dz/(z - a_{1-c})`; in the coordinate `t = z - a_c`, `[t^j] V(a_c + t) (t + δ_c)^{-j-2}`. -/
noncomputable def ebas (c : Fin 2) (j : ℕ) (V : F[X]) : F :=
  coeff j ((Polynomial.taylor (faurePl c) V : PowerSeries F) *
    ((X + PowerSeries.C (faureDel c)) ^ (j + 2))⁻¹)

/-- **The residues of the form `Φ_K^{(c)} = w^{-K} dz/(z - a_c)`** (`lem:residue`, `s = 2`):
`resPhi K c c' V = Res_{a_{c'}}(V Φ_K^{(c)})`. At the own place (`c' = c`, coordinate `t = z - a_c`,
`w = t(t + δ_c)`) the form is `t^{-K-1}(t + δ_c)^{-K} dt`; at the other place it is
`t^{-K}(t + δ_{c'})^{-K-1} dt` (there `z - a_c = t + δ_{c'}`). -/
noncomputable def resPhi (K : ℕ) (c c' : Fin 2) (V : F[X]) : F :=
  if c' = c then
    coeff K ((Polynomial.taylor (faurePl c) V : PowerSeries F) *
      ((X + PowerSeries.C (faureDel c)) ^ K)⁻¹)
  else
    coeff (K - 1) ((Polynomial.taylor (faurePl c') V : PowerSeries F) *
      ((X + PowerSeries.C (faureDel c')) ^ (K + 1))⁻¹)

/-- `w = t + t²`, the frame polynomial `z(z-1)` in the coordinate `t = z - 1` at the place `1`. -/
noncomputable def wLoc : PowerSeries F := X + X ^ 2

lemma isUnit_coeff_one_wLoc : IsUnit (coeff 1 (wLoc : PowerSeries F)) := by
  simp [wLoc, coeff_X_pow]

/-- `w = t (t + δ)`: the frame polynomial `z(z-1)` in the coordinate `t = z - a_c`, `δ = a_c - a_{1-c}`
(stage S11, change of coordinate `w ↔ t`). -/
noncomputable def wD (δ : F) : PowerSeries F := X * (X + PowerSeries.C δ)

/-- **The local root series** `T(w)`: `T + T² = w`, `T(0) = 0` (compositional inverse of `t + t²`). -/
noncomputable def tRoot : PowerSeries F :=
  PowerSeries.substInvOfIsUnit wLoc isUnit_coeff_one_wLoc

/-- The local roots of `z² - z = w` at the places: `z_0(w) = -T(w)`, `z_1(w) = 1 + T(w)`. -/
noncomputable def zF : Fin 2 → PowerSeries F := ![-tRoot, 1 + tRoot]

/-- **`γ(w) = z_1(w)²`**, the curvature series of the Faure frame at the place `1` (`app:machinery`;
also `(z_0(w) - 1)² = γ(w)` at the place `0`). -/
noncomputable def gamF : PowerSeries F := (1 + tRoot) ^ 2

/-- **The e-basis weights** `u_c(w) = 1 / ((dw/dz) · ϖ̂_c(z))` at `z = z_c(w)`, `ϖ̂_c(z) = z - a_{1-c}`:
`u_c = ((2 z_c - 1)(z_c - a_c + δ_c))⁻¹`; in the coordinate `w` the e-basis functional is
`ε_{c,j}(V) = [w^j] u_c(w) V(z_c(w))` (`ebas_eq_w`). The paper's `λ_c φ_c(w) = g_c(w/θ)/u_c(w)`. -/
noncomputable def uF (c : Fin 2) : PowerSeries F :=
  ((PowerSeries.C 2 * zF c - 1) * (zF c - PowerSeries.C (faurePl c) + PowerSeries.C (faureDel c)))⁻¹

/-- **Level-invariant law** (`def:LI`): there are responses `D(l)[c][c']` such that at every level
`K ≥ 1` the one-digit carry responses of the level-`K` law are `D(l)[c][c']`, `1 ≤ l ≤ K` (equivalently,
the own coefficients at carry depths `n ≤ K` and the cross coefficients at carry depths `n ≤ K-1` do not
depend on `K`; the coefficients are the differences of the partial sums `D(l)`). -/
def LevelInv {R : Type*} [CommRing R] {s : ℕ} (C : Gen s R) : Prop :=
  ∃ Dl : ℕ → Fin s → Fin s → R, ∀ K l : ℕ, ∀ c c' : Fin s, 1 ≤ l → l ≤ K →
    IsCarryEntry C K 0 l c c' (Dl l c c')

/-- **The counterexample of `rem:convchar2`** (characteristic two; the instance `X = X' = 1`,
`d_0 = 1`, `d_1 = ω` of the remark): `L_c[n][i] = d_{n+c} binom(2n+1-i, n-i)`, `d_k = 1` for even `k`,
`d_k = ω` for odd `k`. In characteristic two its rows are `η_{c,n} ≡ d_{n+c} e_{c,n}`, i.e.
`T_1 = diag(d_{k+1})`, `T_0 = diag(d_k)`. -/
def convL (ω : F) : Fin 2 → ℕ → ℕ → F :=
  fun c n i => (if (n + (c : ℕ)) % 2 = 0 then 1 else ω) * ((2 * n + 1 - i).choose (n - i) : F)

end GeoSeq
