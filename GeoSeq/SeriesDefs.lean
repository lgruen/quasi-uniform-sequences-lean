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
# GeoSeq stage S1: computable truncated power series (definitions)

A truncated power series with `D` coefficients is a list `L` (`lget L n = [x^n]`, `0` past the end).
These functions are computable (no `Classical.choice`, no field inverse: inverses take the inverse of
the constant term as an argument), so generator entries can be checked by kernel `decide`. The bridge
to `PowerSeries` is `TRep D L φ` (`GeoSeq/Series.lean`).

The generator matrix of a self-similar scramble is computed as in the paper (`sec:WF`): column `k` of
`C_c` is `g_c z_c^k mod x^D`, with `Z ← Z z_c mod x^D` updated from column to column (`tpows`).
-/

namespace GeoSeq

open Finset

variable {R : Type*} [CommRing R]

/-- Coefficient `n` of a truncated series (`0` past the end of the list). -/
def lget (L : List R) (n : ℕ) : R := L.getD n 0

/-- `L` represents `φ` up to `x^D`: `[x^n] φ = lget L n` for `n < D`. -/
def TRep (D : ℕ) (L : List R) (φ : PowerSeries R) : Prop :=
  ∀ n < D, lget L n = PowerSeries.coeff n φ

/-- The constant `c` (`D` coefficients). -/
def tconst (D : ℕ) (c : R) : List R := (List.range D).map fun n => if n = 0 then c else 0

/-- The series `x` (`D` coefficients). -/
def tX (D : ℕ) : List R := (List.range D).map fun n => if n = 1 then 1 else 0

/-- Sum of two truncated series. -/
def tadd (D : ℕ) (a b : List R) : List R := (List.range D).map fun n => lget a n + lget b n

/-- Difference of two truncated series. -/
def tsub (D : ℕ) (a b : List R) : List R := (List.range D).map fun n => lget a n - lget b n

/-- Scalar multiple `C c · a`. -/
def tscale (D : ℕ) (c : R) (a : List R) : List R := (List.range D).map fun n => c * lget a n

/-- Truncated product: `[x^n] = ∑_{i ≤ n} a_i b_{n-i}`. -/
def tmul (D : ℕ) (a b : List R) : List R :=
  (List.range D).map fun n => ((List.range (n + 1)).map fun i => lget a i * lget b (n - i)).sum

/-- The first `n` coefficients of the inverse of `a`, given the inverse `c` of `a_0`:
`b_0 = c`, `b_n = -c ∑_{i<n} a_{i+1} b_{n-1-i}`. -/
def tinvAux (c : R) (a : List R) : ℕ → List R
  | 0 => []
  | n + 1 =>
    let bs := tinvAux c a n
    bs ++ [if n = 0 then c else
      -c * ((List.range n).map fun i => lget a (i + 1) * lget bs (n - 1 - i)).sum]

/-- Truncated inverse (`D` coefficients), given the inverse `c` of the constant term. -/
def tinv (D : ℕ) (c : R) (a : List R) : List R := tinvAux c a D

/-- The first `n` coefficients of `√(1 + a x)` over `ℤ/pℤ`, given `h = 1/2`: the recursion of
`sqrtCoeff` (`ρ_0 = 1`, `ρ_{m+1} = ([m = 0] a - ∑_{i<m} ρ_{i+1} ρ_{m-i}) h`). -/
def tsqrtAux {p : ℕ} (a h : ZMod p) : ℕ → List (ZMod p)
  | 0 => []
  | 1 => [1]
  | m + 2 =>
    let rs := tsqrtAux a h (m + 1)
    rs ++ [((if m = 0 then a else 0) -
      ((List.range m).map fun i => lget rs (i + 1) * lget rs (m - i)).sum) * h]

/-- The powers `1, z, z^2, …, z^{K-1}` mod `x^D`, each from the previous one. -/
def tpowsAux (D : ℕ) (z : List R) : List R → ℕ → List (List R)
  | _, 0 => []
  | Z, K + 1 => Z :: tpowsAux D z (tmul D Z z) K

/-- `[1, z, …, z^{K-1}]` mod `x^D`. -/
def tpows (D : ℕ) (z : List R) (K : ℕ) : List (List R) := tpowsAux D z (tconst D 1) K

/-- The entry `(n, k)` (row `n`, column `k`) of a list of columns. -/
def cget (M : List (List R)) (k n : ℕ) : R := lget (M.getD k []) n

/-- The `D × K` leading block of a self-similar generator matrix `[x^n] g z^k`, column by column. -/
def tcols (D K : ℕ) (g z : List R) : List (List R) := (tpows D z K).map fun Z => tmul D g Z

end GeoSeq
