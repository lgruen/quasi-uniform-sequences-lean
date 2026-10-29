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
public import GeoSeq.V99CovDefs
public import GeoSeq.V93Defs
public import GeoSeq.S10Defs
public import GeoSeq.V95Defs

@[expose] public section

/-!
# GeoSeq stage V10-1 (paper V4, side clauses): definitions

Shared by the statement file `GeoSeq/Statements/V10_1.lean` and the proof files `GeoSeq/V10_1*.lean`
(the formalization notes of the research repository, stage V10-1).

* `rem:randomize`(a), **digital shifts**: `shiftY Y σ` adds the constant digit `σ_{c,n}` to digit `n` of the linear
  coordinate `Y_c` (addition in `F`); the shifted sequence over `ℤ/pℤ` is `linPt p (shiftY Y σ)` (the coordinate is
  affine, not linear, and may have infinitely many nonzero digits).
* **Block-periodic sequences with a smaller free diagonal** (construction found in stage V10-1): the diagonal entries
  of a design are free in `def:block` (reachability constrains only `F_n[i][c]`, `i ≠ c`), so the designs `blk4dF`,
  `blk5dF` keep the off-diagonal entries of `U*_4`, `U*_5` (hence the same design numerators `blk4N`, `blk5N`) and
  replace the diagonal of `F_0` by `-3` resp. `-7` (instead of `-(5,3,5,3)` resp. `-(16,8,12,12,7)`); partial sums
  `blk4dM`, `blk5dM`, entry bounds `blk4dB`, `blk5dB`, checker options `blk4dOpts`, `blk5dOpts` (literal, equal to
  `List.ofFn fun k => caOpts _ (Fin.rev k)`), sequences `blk4d θ`, `blk5d θ`; `Blk5dCA` collects the kernel
  evaluations of the checker for `blk5d` at the primes `23 ≤ p ≤ 61`.
* `rem:randomize`(b), **index scrambles** `C_c ↦ C_c U` with one upper-triangular `U` for all coordinates:
  `idxScr C U` (`(C U)_c[n][j] = ∑_{k ≤ j} C_c[n][k] U[k][j]`, only `U[k][j]`, `k ≤ j`, is used); on index
  polynomials `U` acts by `uMul U V = ∑_j V_j ∑_{k ≤ j} U[k][j] z^k` (`colPoly U j` = column `j`).
-/

namespace GeoSeq

open Finset Polynomial

section Shift
variable {F : Type*} [Field F] {s : ℕ}

/-- **Digital shift** (`rem:randomize`(a)): `y_{c,n}(V) ↦ y_{c,n}(V) + σ_{c,n}`, addition in `F`. -/
def shiftY (Y : Fin s → F[X] → ℕ → F) (σ : Fin s → ℕ → F) : Fin s → F[X] → ℕ → F :=
  fun c V n => Y c V n + σ c n

end Shift

section IdxScr
variable {F : Type*} [Field F] {s : ℕ}

/-- **Index scramble** (`rem:randomize`(b), Faure–Tezuka): `(C U)_c[n][j] = ∑_{k ≤ j} C_c[n][k] U[k][j]` for an
upper-triangular `U` (the entries `U[k][j]`, `k > j`, are not used). -/
def idxScr (C : Gen s F) (U : ℕ → ℕ → F) : Gen s F :=
  fun c n j => ∑ k ∈ range (j + 1), C c n k * U k j

/-- Column `j` of `U` as a polynomial: `∑_{k ≤ j} U[k][j] z^k`. -/
noncomputable def colPoly (U : ℕ → ℕ → F) (j : ℕ) : F[X] :=
  ∑ k ∈ range (j + 1), Polynomial.C (U k j) * X ^ k

/-- The action of `U` on index polynomials: `U V = ∑_j V_j · (column j of U)`. -/
noncomputable def uMul (U : ℕ → ℕ → F) (V : F[X]) : F[X] :=
  V.sum fun j a => Polynomial.C a * colPoly U j

end IdxScr

section Diag

/-- **`thm:block`(c), `s = 4`, smaller diagonal**: `U*_4` with the diagonal of `F_0` replaced by `-3`. -/
def blk4dF : ℕ → Fin 4 → Fin 4 → ℤ := fun n i c => if n = 0 ∧ i = c then -3 else blk4F n i c

/-- The partial sums `M^{(j)}` of `blk4dF` (checked in the proof module). -/
def blk4dM : ℕ → Fin 4 → Fin 4 → ℤ := fun n =>
  if n = 0 then !![-3, 2, 1, 2; 1, -3, -1, -1; 1, 2, -3, -2; 1, 1, 1, -3]
  else if n = 1 then !![-3, -1, 0, 1; -1, -3, 1, 0; 0, 1, -3, 1; 1, 0, 1, -3]
  else !![-3, 1, 0, 0; 1, -3, -1, 0; 0, 0, -3, -1; 0, 0, 0, -3]

/-- Entry bounds `B_{ic} = max_j |M^{(j)}[i][c]|` of `blk4dF` (row sums `≤ 8`). -/
def blk4dB : Fin 4 → Fin 4 → ℤ := !![3, 2, 1, 2; 1, 3, 1, 1; 1, 2, 3, 2; 1, 1, 1, 3]

/-- The options of the checker for `blk4dF` (literal). -/
def blk4dOpts : List (List (ℤ × ℤ)) :=
  [[(0, 0), (64, -50462974), (64, -50266111), (64, -50397184), (128, 50462974), (128, 50266111), (128, 50397184)],
   [(0, 0), (16, 16580353), (16, 16580864), (16, -196864), (32, -16580353), (32, -16580864), (32, 196864)],
   [(0, 0), (4, 16907522), (4, 64767), (4, -767), (8, -16907522), (8, -64767), (8, 767)],
   [(0, 0), (1, 16843005), (1, 16776957), (1, 253), (2, -16843005), (2, -16776957), (2, -253)]]

/-- **`thm:block`(c), `s = 5`, smaller diagonal**: `U*_5` with the diagonal of `F_0` replaced by `-7`. -/
def blk5dF : ℕ → Fin 5 → Fin 5 → ℤ := fun n i c => if n = 0 ∧ i = c then -7 else blk5F n i c

/-- The partial sums `M^{(j)}` of `blk5dF` (checked in the proof module). -/
def blk5dM : ℕ → Fin 5 → Fin 5 → ℤ := fun n =>
  if n = 0 then !![-7, 6, 2, 2, 6; 1, -7, -2, -1, -2; 1, 6, -7, -2, -3; 1, 3, 2, -7, -6; 1, 2, 1, 2, -7]
  else if n = 1 then !![-7, -5, -1, 1, 5; -2, -7, 3, 0, -1; -1, 1, -7, 1, -1; 0, -1, 1, -7, 1; 1, -1, 0, 3, -7]
  else if n = 2 then !![-7, 1, -1, -1, 1; 0, -7, 0, 0, 0; -1, 2, -7, -2, 0; -1, 0, 2, -7, -2; 0, 0, 0, 0, -7]
  else !![-7, 0, 0, 0, 0; -1, -7, 1, 0, 0; 0, 1, -7, 0, 0; 0, 0, 0, -7, 1; 0, 0, 0, 1, -7]

/-- Entry bounds `B_{ic} = max_j |M^{(j)}[i][c]|` of `blk5dF` (row sums `≤ 23`). -/
def blk5dB : Fin 5 → Fin 5 → ℤ :=
  !![7, 6, 2, 2, 6; 2, 7, 3, 1, 2; 1, 6, 7, 2, 3; 1, 3, 2, 7, 6; 1, 2, 1, 3, 7]

/-- The options of the checker for `blk5dF` (literal). -/
def blk5dOpts : List (List (ℤ × ℤ)) :=
  [[(0, 0), (256, -30165631482), (256, -30048059643), (256, -30098325503), (256, -30047993856), (512, 30165631482), (512, 30048059643), (512, 30098325503), (512, 30047993856)],
   [(0, 0), (64, 8472362754), (64, 12767526913), (64, -117571585), (64, 4177526784), (128, -8472362754), (128, -12767526913), (128, 117571585), (128, -4177526784)],
   [(0, 0), (16, 4328062466), (16, 16319231), (16, 33095679), (16, -458496), (32, -4328062466), (32, -16319231), (32, -33095679), (32, 458496)],
   [(0, 0), (4, 8640657670), (4, -4311680773), (4, 129281), (4, 63744), (8, -8640657670), (8, 4311680773), (8, -129281), (8, -63744)],
   [(0, 0), (1, 4311810297), (1, 4294901241), (1, -16842759), (1, -263), (2, -4311810297), (2, -4294901241), (2, 16842759), (2, 263)]]

/-- The primes `23 ≤ p ≤ 61` (the range below the written argument for `blk5dF`). -/
def blk5dCAPrimes : List ℕ := [23, 29, 31, 37, 41, 43, 47, 53, 59, 61]

/-- The kernel evaluations of the checker for `blk5dF` (`A = 7`) at the primes `23 ≤ p ≤ 61`. -/
def Blk5dCA : Prop := ∀ q ∈ blk5dCAPrimes, caCheck 5 blk5dOpts blk5St0 q 7 = true

variable {p : ℕ} [Fact p.Prime]

/-- The block-periodic residue sequence with `ℓ = s = 4`, places `(0, 1, 1/2, 1/3)`, `v = (1, 1, 2, 3)`, design
`blk4dF` (same design numerators `blk4N` as `blk4`: identity (a) of `def:block` involves only off-diagonal entries). -/
noncomputable def blk4d (θ : ZMod p) : Gen 4 (ZMod p) :=
  blockGen blk4a θ 4 blk4v (blockF blk4dF) blk4N 1

/-- The block-periodic residue sequence with `ℓ = s = 5`, places `(0, 1, 1/2, 1/3, 1/4)`, `v = (1, 1, 2, 3, 4)`, design
`blk5dF` (same design numerators `blk5N` as `blk5`). -/
noncomputable def blk5d (θ : ZMod p) : Gen 5 (ZMod p) :=
  blockGen blk5a θ 5 blk5v (blockF blk5dF) blk5N 1

end Diag

end GeoSeq
