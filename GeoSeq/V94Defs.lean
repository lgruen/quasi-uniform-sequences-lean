/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs
public import GeoSeq.S11Defs

@[expose] public section

/-!
# GeoSeq stage V9-4 (paper V4): definitions for staggered residue sequences

Shared by the statement file `GeoSeq/Statements/V94.lean` and the proof files `GeoSeq/V94*.lean`.

* **Staggered residue sequence** (`def:residuestar`). Staggered coordinate `c⋆` (`cs`), scale `θ`, constant
  `μ⋆` (`μs`) and weights `k_c` (`c ≠ c⋆`; the value `k cs` is not used); `μ_c = -μ⋆/k_c` (`stagMu`). Digit `n` of
  coordinate `c` is `μ_c Res_{a_c}(V dz / ((z - a_{c⋆}) (w/θ)^{N}))` with `N = n + 1` for `c ≠ c⋆` and `N = n` for
  `c = c⋆` (`stagLev`). The denominator `(z - a_{c⋆}) w^N` is `placePoly a (stagK cs N)` (pole orders `N + 1` at
  `a_{c⋆}`, `N` elsewhere), and the pole order at the own place is always `n + 1`. The scramble `resStarL`
  (`L_c[n][i] = μ_c θ^N [t^{n-i}] U_c(a_c + t)^{-1}`, `U_c` the cofactor `placeCo` of `(z - a_c)^{n+1}`) gives
  `resStar = scrGen a resStarL`, i.e. `C_c = L_c P_{a_c}` (`lem:residuestar-t0`); the paper's entry formula is
  `resStar_apply_ne` / `resStar_apply_self`, the residue reading `resStar_digit`.
* **The certificate constant** (`thm:residuestar`): the centred absolute value `cabsZ` of `x ∈ ℤ/pℤ`
  (`min(val x, p - val x)`), the steps `e' ∈ {-1,0,1}^C \ {0}` (`StarStep`: `e` vanishes at `c⋆`), and
  `β(k) = min_{e'} (cabsZ(k · e') - 1)/p` (`betaStar`, an infimum over the steps).
* **Dyadic weights** (`cor:dyadic`): `k_c = 2^{o(c)} / 2^{s-1}` (`dyadicK`), with an order `o` of the coordinates
  `C` (`o` injective on `C` with values `< s - 1`; the paper's `c_i` has `o(c_i) = i - 1`).
* **The brick wall** (`ex:brickwall`, `def:WF`): `s = 2`, Faure places `(0, 1)`, `c⋆ = 1`, `θ = -1/4`,
  `μ⋆ = 2`, `k_0 = 1/2` (so `μ_0 = -4`) — `brickWall`.
-/

namespace GeoSeq

open Finset Polynomial

section Star
variable {F : Type*} [Field F] {s : ℕ}

/-- The pole orders of `1/((z - a_{c⋆}) w^N)`: `N + 1` at `a_{c⋆}`, `N` at the other places. -/
def stagK (cs : Fin s) (N : ℕ) : Fin s → ℕ := fun c => if c = cs then N + 1 else N

/-- The exponent `N` of `(w/θ)^N` that reads digit `n` of coordinate `c` (`def:residuestar`): `n + 1` for
`c ≠ c⋆`, `n` for `c = c⋆`. -/
def stagLev (cs c : Fin s) (n : ℕ) : ℕ := if c = cs then n else n + 1

/-- The row constants `μ_{c⋆} = μ⋆`, `μ_c = -μ⋆/k_c` (`c ≠ c⋆`). -/
noncomputable def stagMu (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s) : F :=
  if c = cs then μs else -μs / k c

/-- The scramble of the staggered residue sequence (`lem:residuestar-t0`):
`L_c[n][i] = μ_c θ^N [t^{n-i}] U(a_c + t)^{-1}`, `N = stagLev cs c n`, `U = placeCo a (stagK cs N) c` (the
cofactor of `(z - a_c)^{n+1}` in `(z - a_{c⋆}) w^N`; only `i ≤ n` is used by `scrGen`). -/
noncomputable def resStarL (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) :
    Fin s → ℕ → ℕ → F :=
  fun c n i => stagMu cs μs k c * θ ^ stagLev cs c n *
    PowerSeries.coeff (n - i)
      ((taylor (a c) (placeCo a (stagK cs (stagLev cs c n)) c) : PowerSeries F)⁻¹)

/-- **The staggered residue sequence** `𝓡^⋆_v` (`def:residuestar`) with places `a`, scale `θ`, staggered
coordinate `cs`, constant `μs` and weights `k` (check vector `v_c = k_c`, `v_{c⋆} = -1`): `C_c = L_c P_{a_c}`,
`L_c = resStarL`. Digit `n` of coordinate `c ≠ c⋆` is `μ_c Res_{a_c}(V dz/((z - a_{c⋆})(w/θ)^{n+1}))`, digit `n`
of `c⋆` is `μ⋆ Res_{a_{c⋆}}(V dz/((z - a_{c⋆})(w/θ)^n))` (`resStar_digit`). -/
noncomputable def resStar (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) : Gen s F :=
  scrGen a (resStarL a θ cs μs k)

end Star

section Beta
variable {s : ℕ}

/-- The centred absolute value `|x|_∘ ∈ [0, p/2]` of `x ∈ ℤ/pℤ`: `min(val x, p - val x)`. -/
def cabsZ {p : ℕ} (x : ZMod p) : ℕ := min x.val (p - x.val)

/-- The steps of `thm:residuestar`: `e ∈ {-1,0,1}^s` with `e_{c⋆} = 0` and `e ≠ 0` (i.e. `e' ∈ {-1,0,1}^C \ {0}`). -/
def StarStep (cs : Fin s) (e : Fin s → ℤ) : Prop :=
  (∀ c, -1 ≤ e c ∧ e c ≤ 1) ∧ e cs = 0 ∧ ∃ c, e c ≠ 0

/-- `β(k) = min_{e' ∈ {-1,0,1}^C \ {0}} (|k · e'|_∘ - 1)/p` (`thm:residuestar`), as an infimum over the steps
(nonempty for `s ≥ 2`, bounded below by `-1/p`). -/
noncomputable def betaStar (p : ℕ) (cs : Fin s) (k : Fin s → ZMod p) : ℝ :=
  ⨅ e : {e : Fin s → ℤ // StarStep cs e}, ((cabsZ (∑ c, (e.1 c : ZMod p) * k c) : ℝ) - 1) / p

/-- The dyadic weights `k_c = 2^{o(c)} / 2^{s-1} ∈ ℤ/pℤ` (`cor:dyadic`; `o(c_i) = i - 1`). -/
noncomputable def dyadicK (p : ℕ) (o : Fin s → ℕ) : Fin s → ZMod p :=
  fun c => (2 : ZMod p) ^ o c * ((2 : ZMod p)⁻¹) ^ (s - 1)

/-- The standard order of the coordinates `C = {c ≠ c⋆}` (`cor:dyadic`): `o(c) = c` for `c < c⋆` and `o(c) = c - 1`
for `c > c⋆`, so `o` maps `C` bijectively onto `{0, …, s - 2}`. -/
def stdOrder (cs c : Fin s) : ℕ := if (c : ℕ) < cs then c else c - 1

/-- **The brick wall** `W^-` in the V4 definition (`ex:brickwall`, `def:WF`): the staggered residue sequence with
`s = 2`, the Faure places `a = (0, 1)`, staggered coordinate `c⋆ = 1`, `θ = -1/4`, `μ⋆ = 2` and weight
`k_0 = 1/2` (so `μ_0 = -μ⋆/k_0 = -4`). -/
noncomputable def brickWall (p : ℕ) [Fact p.Prime] : Gen 2 (ZMod p) :=
  resStar faurePl (-(4 : ZMod p)⁻¹) 1 2 ![(2 : ZMod p)⁻¹, 0]

end Beta

end GeoSeq
