/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Defs
public import GeoSeq.V97Defs

@[expose] public section

/-!
# GeoSeq stage V10-2 (paper V4, `def:selfsim`, `lem:resform`(b), `lem:reschange`): definitions

Over a field `F`, places `a_c`, `w = ∏_c (z - a_c)`, scale `θ`.

* `IsLocRoots a θ zθ`: `zθ c = z_c(θx)` are the **scaled local roots** of `def:selfsim`: `zθ_c(0) = a_c` and
  `w(zθ_c(x)) = θx` (the paper's `z_c(x)` with `w(z_c(x)) = x`, read at `θx`).
* `IsSelfSim a θ g L`: **`def:selfsim` as written** — the scramble `L` of the frame is self-similar with scale `θ`
  and unit multipliers `g_c`: its generator matrices are `C_c[n][k] = [x^n] g_c(x) z_c(θx)^k`
  (`scrGen a L = ssGen g zθ`) for the scaled local roots.
* `locU a θ c = w(a_c + t)/θ ∈ F[t]` (the substitution `u = w/θ` at `a_c`, in `t = z - a_c`).
* `locMul a θ g c = g_c(u(t)) u'(t) = θ^{-1} g_c(w/θ) w'` at `a_c` (`lem:resform`(b): `g_c ↦ φ_c`).
* `ssMul a zθ φ c = φ_c(zθ_c(x) - a_c) zθ_c'(x) = θ φ_c(z_c(θx)) z_c'(θx)` (`lem:resform`(b): `φ_c ↦ g_c`).
* `corrV`, `corrCoef`: `v_c` and the correction coefficients `χ_{c,d}` of `lem:corrS` for a self-similar scramble
  with multipliers `g_c`: `v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)`.
* `truncN a φ K c`: the polynomial `N_c` with `N_c(a_c + t) = φ_c mod t^K` (the rational residue form `ssResGen a θ N 1`
  has the rows `< K` of `ssL a θ φ`).
* `CorrTruncPS`: the correction coefficients of a power-series local multiplier up to order `K` (`lem:corrS`):
  `1/φ_c = v_c ∑_{d<K} χ_{c,d} (w/θ)^d + O(w^K)` at `a_c`, written `t^K ∣ 1 - v_c φ_c ∑_{d<K} χ_{c,d} u^d`.
-/

namespace GeoSeq

open Finset Polynomial

section SS
variable {F : Type*} [Field F] {s : ℕ}

/-- The **scaled local roots** `zθ_c = z_c(θx)` of `def:selfsim`: constant term `a_c` and `w(zθ_c) = θx`. -/
def IsLocRoots (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F) : Prop :=
  ∀ c, PowerSeries.constantCoeff (zθ c) = a c ∧
    Polynomial.aeval (zθ c) (wPoly a) = PowerSeries.C θ * PowerSeries.X

/-- **`def:selfsim` as written**: the scramble `L` of the frame with places `a` is self-similar with scale `θ` and
unit multipliers `g_c` — `C_c[n][k] = [x^n] g_c(x) z_c(θx)^k` for the scaled local roots `z_c(θx)`. -/
def IsSelfSim (a : Fin s → F) (θ : F) (g : Fin s → PowerSeries F) (L : Fin s → ℕ → ℕ → F) : Prop :=
  (∀ c, PowerSeries.constantCoeff (g c) ≠ 0) ∧ ∃ zθ, IsLocRoots a θ zθ ∧ scrGen a L = ssGen g zθ

/-- The substitution `u = w/θ` at the place `a_c`, as a polynomial in `t = z - a_c`: `u(t) = θ^{-1} w(a_c + t)`. -/
noncomputable def locU (a : Fin s → F) (θ : F) (c : Fin s) : F[X] := C θ⁻¹ * taylor (a c) (wPoly a)

/-- **The local multipliers of a self-similar scramble** (`lem:resform`(b)):
`φ_c(z) = θ^{-1} g_c(w(z)/θ) w'(z)`, i.e. `φ_c(a_c + t) = g_c(u(t)) u'(t)`. -/
noncomputable def locMul (a : Fin s → F) (θ : F) (g : Fin s → PowerSeries F) (c : Fin s) : PowerSeries F :=
  (g c).subst (locU a θ c : PowerSeries F) * ((Polynomial.derivative (locU a θ c) : F[X]) : PowerSeries F)

/-- **The multipliers of a residue form** (`lem:resform`(b)): `g_c(x) = θ φ_c(z_c(θx)) z_c'(θx)`, i.e.
`g_c = φ_c(zθ_c - a_c) · zθ_c'` with `zθ_c = z_c(θx)` (`φ_c` a series in `t = z - a_c`). -/
noncomputable def ssMul (a : Fin s → F) (zθ φ : Fin s → PowerSeries F) (c : Fin s) : PowerSeries F :=
  (φ c).subst (zθ c - PowerSeries.C (a c)) * PowerSeries.derivative (zθ c)

/-- **Correction coefficients of power-series local multipliers up to order `K`** (`lem:corrS`):
`1/φ_c = v_c ∑_{d<K} χ_{c,d} (w/θ)^d + O(w^K)` at `a_c`, i.e. `t^K ∣ 1 - v_c φ_c ∑_{d<K} χ_{c,d} u^d` in `F[[t]]`. -/
def CorrTruncPS (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (K : ℕ) : Prop :=
  ∀ c, (PowerSeries.X : PowerSeries F) ^ K ∣ 1 - PowerSeries.C (v c) * φ c *
    ∑ d ∈ range K, PowerSeries.C (χ c d) * (locU a θ c : PowerSeries F) ^ d

/-- `v_c = 1/φ_c(a_c)` of `lem:corrS` for a self-similar scramble with multipliers `g_c` and scaled local roots
`zθ_c`: `v_c = [x] zθ_c / g_c(0)` (`corrV_eq`). -/
noncomputable def corrV (zθ g : Fin s → PowerSeries F) (c : Fin s) : F :=
  PowerSeries.coeff 1 (zθ c) / PowerSeries.constantCoeff (g c)

/-- **The correction coefficients** of `lem:corrS` for a self-similar scramble (`def:selfsim`) with multipliers `g_c`:
`v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)` (`= θ z_c'(θx)/g_c(x)`), equivalently `1/φ_c = v_c ∑_d χ_{c,d} (w/θ)^d` at
`a_c` (`corrTruncPS_corrCoef`). -/
noncomputable def corrCoef (zθ g : Fin s → PowerSeries F) (c : Fin s) (d : ℕ) : F :=
  PowerSeries.coeff d (PowerSeries.derivative (zθ c) * (g c)⁻¹) / corrV zθ g c

/-- The polynomial `N_c` with `N_c(a_c + t) = φ_c mod t^K`. -/
noncomputable def truncN (a : Fin s → F) (φ : Fin s → PowerSeries F) (K : ℕ) (c : Fin s) : F[X] :=
  (PowerSeries.trunc K (φ c)).comp (X - C (a c))

end SS

end GeoSeq
