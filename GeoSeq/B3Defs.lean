/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SeriesDefs

@[expose] public section

/-!
# GeoSeq stage S6: definitions for `thm:B3` (polynomial lists, automaton states, initial states)

Shared by the statement files and the proof files (house convention: statements use only
definitions from `*Defs` modules). Proofs: `GeoSeq/B3Auto.lean`, `GeoSeq/B3Law.lean`,
`GeoSeq/B3Cert.lean`.
-/

namespace GeoSeq

open Finset PowerSeries

section Lists

variable {R : Type*} [CommRing R]

/-- The polynomial `∑_n L_n x^n` of a list, as a power series. -/
noncomputable def lps (L : List R) : PowerSeries R := PowerSeries.mk (lget L)

/-- Coefficientwise sum of two lists. -/
def padd : List R → List R → List R
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: padd a b

/-- Product of two polynomials given as lists. -/
def pmul : List R → List R → List R
  | [], _ => []
  | x :: a, b => padd (b.map (x * ·)) (0 :: pmul a b)

/-- Negation of a list. -/
def pneg (L : List R) : List R := L.map (- ·)

/-- Multiplication by `x^k`. -/
def pshift (k : ℕ) (L : List R) : List R := List.replicate k 0 ++ L

/-- The coefficients `k, k+3, k+6, …` of a list (the Cartier operator `Λ_k` on polynomials, `k < 3`). -/
def ev3 : ℕ → List R → List R
  | _, [] => []
  | 0, x :: r => x :: ev3 2 r
  | k + 1, _ :: r => ev3 k r

/-- Removing trailing zeros (canonical form). -/
def trim [DecidableEq R] : List R → List R
  | [] => []
  | x :: xs => if trim xs = [] ∧ x = 0 then [] else x :: trim xs

/-- The Cartier operator `Λ_r F = ∑_k [x^{3k+r}] F · x^k` (base `3`). -/
noncomputable def lam3 (r : ℕ) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k => coeff (3 * k + r) F

end Lists

/-- The polynomial `Q_p = 2 + x² = -(1 - x²)` (the part of the common denominator prime to `x`). -/
def Qp3 : List (ZMod 3) := [2, 0, 1]

/-- `x^16 Q_p²` (the factor `x^{2d} Q_p^{q-1}` of the Cartier step, `d = 8`). -/
def W3 : List (ZMod 3) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1]

/-- `x^16 Q_p² (1 + x)` (the same with the Mahler factor `A = 1 + x` of `τ^{-1}`). -/
def Wx3 : List (ZMod 3) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]

/-- A state: numerators `(P_0, P_1)` of `x^{-8}(P_0 + P_1 τ^{-1})/Q_p`. -/
abbrev St3 := List (ZMod 3) × List (ZMod 3)

/-- The power series `(P_0 + P_1 τ^{-1}) Q_p^{-1}`; coefficient `n + 8` of it is coefficient `n` of
the state. -/
noncomputable def esem (S : St3) : PowerSeries (ZMod 3) := (lps S.1 + lps S.2 * T3) * (lps Qp3)⁻¹

/-- The Cartier step `Λ_r` on numerators:
`(P_0, P_1) ↦ (Λ_r(x^16 Q_p² P_0), Λ_r(x^16 Q_p² (1+x) P_1))` (trimmed). -/
def stepP (r : ℕ) (S : St3) : St3 :=
  (trim (ev3 r (pmul S.1 W3)), trim (ev3 r (pmul S.2 Wx3)))

/-- The first `D` coefficients of `τ^{-1}`. -/
def T3L (D : ℕ) : List (ZMod 3) := (List.range D).map t3c

/-- Coefficient `n` (`n < D`) of `(P_0 + P_1 τ^{-1}) Q_p^{-1}`, computed with truncated series. -/
def acoefN (D : ℕ) (S : St3) (n : ℕ) : ZMod 3 :=
  lget (tmul D (tadd D S.1 (tmul D S.2 (T3L D))) (tinv D 2 Qp3)) n

/-- The readout `[x^0]` of a state (coefficient `8` of `esem`). -/
def acoef (S : St3) : ZMod 3 := acoefN 9 S 8

/-- The coefficients `n` of a vector of states. -/
noncomputable def vals (V : List St3) (n : ℕ) : List (ZMod 3) :=
  V.map fun S => coeff (n + 8) (esem S)

/-- One Cartier step on a vector of states. -/
def stepV (r : ℕ) (V : List St3) : List St3 := V.map (stepP r)

/-- Reading the base-3 digits of `n` (least significant first). -/
def readV : List ℕ → List St3 → List St3
  | [], V => V
  | r :: ds, V => readV ds (stepV r V)

/-- Numerators of the frame matrix over `Q_p`: `M[c][b] = esem (B3Mn c b)` (`B3_M`). -/
def B3Mn : Fin 2 → Fin 2 → St3 :=
  ![![([1, 1, 2, 2], [1, 0, 0, 1]), ([0, 2, 1, 2], [0, 2, 0, 0, 2])],
    ![([1, 0, 2], [1, 0, 2]), ([1, 0, 2], [1, 2, 2, 1])]]

/-- Numerators of `Ĝ = G/(1-x)` over `x² Q_p` (`B3_ghat`). -/
def B3An : Fin 2 → Fin 2 → St3 :=
  ![![([0, 1, 2], [0, 2, 1]), ([0, 1, 0, 2], [0, 2, 1, 2])],
    ![([1, 2], [2, 2, 2]), ([0, 2, 2], [0, 1, 2, 1])]]

/-- The coefficients `m_a[c][b] = [x^a] M[c][b]`, `a < 6` (computable). -/
def B3mtab (c b : Fin 2) (a : ℕ) : ZMod 3 := acoefN 6 (B3Mn c b) a

/-- `M_{≤ i}[c][b] = ∑_{a ≤ i} m_a[c][b] x^a` as a list. -/
def B3Mle (i : ℕ) (c b : Fin 2) : List (ZMod 3) := (List.range (i + 1)).map (B3mtab c b)

/-- The initial state of entry `(c, c')`, depth `i`: numerators of
`x^{-i}(δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c'])` (over `x^8 Q_p`; `-1 = 2`). -/
def initS (i : ℕ) (c c' : Fin 2) : St3 :=
  (trim (pshift (6 - i) (padd (if c = c' then [0, 0, 2, 2] else [])
      ((padd (pmul (B3Mle i c 0) (B3An 0 c').1) (pmul (B3Mle i c 1) (B3An 1 c').1)).map (2 * ·)))),
   trim (pshift (6 - i)
      ((padd (pmul (B3Mle i c 0) (B3An 0 c').2) (pmul (B3Mle i c 1) (B3An 1 c').2)).map (2 * ·))))

/-- The initial vector of column `c'`: entry `2i + c` is `initS i c c'` (`i < 6`). -/
def initV (c' : Fin 2) : List St3 :=
  (List.range 12).map fun k => initS (k / 2) (if k % 2 = 0 then 0 else 1) c'

/-- The series `F_i[c][c'] = δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c']` (written with `2 = -1`). -/
noncomputable def B3F (i : ℕ) (c c' : Fin 2) : PowerSeries (ZMod 3) :=
  (if c = c' then PowerSeries.mk 1 else 0) +
    2 * ∑ b : Fin 2, (∑ a ∈ range (i + 1), C (coeff a (frameM B3g B3z c b)) * X ^ a) *
      (B3G b c' * PowerSeries.mk 1)

end GeoSeq
