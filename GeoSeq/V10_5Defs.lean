/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Defs
public import GeoSeq.V9Defs
public import GeoSeq.V7Defs
public import Z3Net.FDefs
public import GeoSeq.SeqNet

@[expose] public section

/-!
# GeoSeq stage V10-5 (paper V4, `sec:hammersley`): definitions

Shared by the statement file `GeoSeq/Statements/V10_5.lean` and the proof files `GeoSeq/V10_5*.lean`
(the formalization notes of the research repository, stage V10-5).

* **The Hammersley lift** `P̂_m = {(v q^{-m}, y(v)) : v < q^m} ⊂ [0,1)^{s+1}` (`liftPt`, index coordinate first), and
  the lift of a digitally shifted sequence (`liftPtSh`, digits `y_{c,n}(v) + ς_{c,n}`, `shPoint` of `lem:shift`).
* **Its generator matrices** (`prop:liftslab`(i)): the reversal matrix `revMat m` (`R[i][j] = 1` iff `i + j = m - 1`)
  for the index coordinate, then the leading `m × m` blocks `truncGen C m` of the `C_c` (`liftGen`).
* **The net property of the lift in the library's box form** (`LiftNet0`): every elementary box with `d_0` digits in
  the index coordinate and `d_c` digits in coordinate `c` (`∑ d = m`) holds exactly one index `v < q^m`; the index
  coordinate `v/q^m` lies in the `a`-th interval of length `q^{-d_0}` iff `v / q^{m - d_0} = a` (`lift_first_box`), the
  other coordinates are read by `cellIdx` as in `BlockNet0`.
* **Slabs** (`sec:hammersley`): two indices are in the same `K_0`-slab iff `v / q^{m-K_0} = w / q^{m-K_0}`.
* **The carry pair of `prop:liftcarry`**: `carryI p k ℓ = (p^ℓ - 1) p^k`, `carryJ p k ℓ = p^{k+ℓ}`; the order of
  vanishing used at the place `a` (`liftOrd`): `k` at `0`, `p^r - 1` at `1`, `p^r` at the other `n`-th roots of unity.
* **The toroidal minimum distance** `δ(P) = 2 q(P)` (`Z3NetDGS.sepRad`, toroidal Euclidean) of the first `N` points
  (`liftDelta`).
-/

namespace GeoSeq

open Finset

section Lift

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **The Hammersley lift** (`sec:hammersley`): the point `(v q^{-m}, y(v)) ∈ [0,1)^{s+1}` of `P̂_m`, index
coordinate first. -/
noncomputable def liftPt (D : DigitCode R q) (C : Gen s R) (m v : ℕ) : Fin (s + 1) → ℝ :=
  Fin.cons ((v : ℝ) / (q : ℝ) ^ m) (seqPoint D C v)

/-- The Hammersley lift of the digitally shifted sequence (digits `y_{c,n}(v) + ς_{c,n}`; `lem:shift`). -/
noncomputable def liftPtSh (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) (m v : ℕ) : Fin (s + 1) → ℝ :=
  Fin.cons ((v : ℝ) / (q : ℝ) ^ m) (shPoint D C ς v)

/-- The reversal matrix: `R[i][j] = 1` iff `i + j = m - 1`. -/
def revMat (m : ℕ) : Matrix (Fin m) (Fin m) R := fun i j => if (i : ℕ) + (j : ℕ) + 1 = m then 1 else 0

/-- **The generator matrices of the lift** (`prop:liftslab`(i)): the reversal matrix for the index coordinate, then
the leading `m × m` blocks of the `C_c`. -/
def liftGen (C : Gen s R) (m : ℕ) : Fin (s + 1) → Matrix (Fin m) (Fin m) R :=
  Fin.cons (revMat m) (truncGen C m)

/-- **The lift is a `(0,m,s+1)`-net** (box form, as `BlockNet0`): for every `d` with `∑_c d_c = m` and every box `a`,
exactly one index `v < q^m` has its index coordinate in the box `a_0` with `d_0` digits (`v / q^{m-d_0} = a_0`) and
`cellIdx` `a_{c+1}` with `d_{c+1}` digits in coordinate `c`. -/
def LiftNet0 (D : DigitCode R q) (C : Gen s R) (m : ℕ) : Prop :=
  ∀ d : Fin (s + 1) → ℕ, ∑ c, d c = m → ∀ a : Fin (s + 1) → ℕ, (∀ c, a c < q ^ d c) →
    ∃! v : ℕ, v < q ^ m ∧ v / q ^ (m - d 0) = a 0 ∧ ∀ c : Fin s, cellIdx D C v c (d c.succ) = a c.succ

end Lift

section Carry

/-- The first index of the carry pair of `prop:liftcarry`: `i = (p^ℓ - 1) p^k` (digits `p - 1` at `k, …, k+ℓ-1`). -/
def carryI (p k l : ℕ) : ℕ := (p ^ l - 1) * p ^ k

/-- The second index of the carry pair: `j = p^{k+ℓ}` (`j - i = p^k`). -/
def carryJ (p k l : ℕ) : ℕ := p ^ (k + l)

/-- The order of vanishing of `D = V_j - V_i` used at the place `a` in the proof of `prop:liftcarry` (`ℓ + 1 = n p^r`):
`k` at `0`, `p^r - 1` at `1`, `p^r` at every other place (an `n`-th root of unity `≠ 1`). -/
def liftOrd {F : Type*} [Zero F] [One F] [DecidableEq F] (p r k : ℕ) (a : F) : ℕ :=
  if a = 0 then k else if a = 1 then p ^ r - 1 else p ^ r

end Carry

/-- **The minimum distance** `δ = 2 q(P)` (toroidal Euclidean, `Z3NetDGS.sepRad`) of the first `N` points of `pt`;
`liftDelta (liftPt D C m) (q^m)` is `δ(P̂_m)`. -/
noncomputable def liftDelta {d : ℕ} (pt : ℕ → Fin d → ℝ) (N : ℕ) : ℝ :=
  2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N pt)

end GeoSeq
