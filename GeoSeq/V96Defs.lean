/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Defs
public import GeoSeq.V94Defs

@[expose] public section

/-!
# GeoSeq stage V9-6 (paper V4, `sec:block`): definitions for block-periodic residue sequences

Shared by the statement file `GeoSeq/Statements/V96.lean` and the proof files `GeoSeq/V96*.lean`.

* **Multipliers as numerators** (`def:block`). Every local multiplier at the place `a_c` is written
  `φ_{c,j} = N_{c,j} / w_c` with a polynomial numerator `N_{c,j}` (`w_c = ∏_{c' ≠ c} (z - a_{c'})`; `u_i = 1/(z - a_i)`
  is `wCoCo c i / w_c` for `i ≠ c`). With `Ω = w^ℓ/θ`, digit `ℓn + j` of coordinate `c` is
  `Res_{a_c}(V φ_{c,j} Ω^{-(n+1)} dz) = θ^{n+1} Res_{a_c}(V N_{c,j} / (w_c w^{ℓ(n+1)}) dz)`
  `= θ^{n+1} Res_{a_c}(V N_{c,j} / ((z - a_c)^{ℓ(n+1)} w_c^{ℓ(n+1)+1}) dz)` (`blockDig`, with `locRes`).
* `blockNum`: (a) the **design numerators** `N_{c,ℓ-1-n}` (`n ≤ s-2`) are data (`Nd c (ℓ-1-n)`; for the instances they are
  computed from the design by solving (a), and (a) is checked as a polynomial identity); (b) the **skeleton numerators**
  `N_{c,j} = w^{ℓ-1-j} w_c / v'_c` (`1 ≤ j ≤ ℓ-s`); (c) the **own numerator**
  `N_{c,0} = θ^{-1} (v_c^{-1} w^{ℓ-1} w_c² + w^ℓ ∑_n F_n[c][c] N_{c,ℓ-1-n})` (that is `w_c φ_{c,0}` for
  `φ_{c,0} = v_c^{-1} Ω u_c + Ω ∑_n F_n[c][c] φ_{c,ℓ-1-n}`).
* `blockGen`: the generator matrices `C_c[d][k] = blockDig c d (z^k)`.
* The design is given by integer matrices `Fz n i c = F_n[i][c]` read in the field (`blockF`).
* **Instances**: `blk2` (`thm:block`(a): `s = 2`, places `(0,1)`, `v = (1,1)`, `F_0 = ((-1,1),(-1,-1))`), `blk3`
  (`thm:block`(b): `s = 3`, places `(0,2,1)`, `v = (1/2,1/2,-1)`, `(F_0,F_1) = (M,J)`), `gaussGen` (`cor:gauss`:
  `s = 2`, places `(0,1)`, `v = (-u,-1)`, `F_0 = ((-1,u),(-u,-1))`).
-/

namespace GeoSeq

open Finset Polynomial

section Block
variable {F : Type*} [Field F] {s : ℕ}

/-- `∏_{i' ≠ c, i} (z - a_{i'})`, so that `u_i = 1/(z - a_i) = wCoCo a c i / w_c` for `i ≠ c`. -/
noncomputable def wCoCo (a : Fin s → F) (c i : Fin s) : F[X] := ∏ i' ∈ (univ.erase c).erase i, (X - C (a i'))

/-- The design matrices `F_n[i][c]` (`n ≤ s - 2`) of integers, read in the field. -/
def blockF (Fz : ℕ → Fin s → Fin s → ℤ) : ℕ → Fin s → Fin s → F := fun n i c => (Fz n i c : F)

/-- **The numerators** `N_{c,j} = w_c φ_{c,j}` of the local multipliers of `def:block`: (c) own (`j = 0`), (b) skeleton
(`1 ≤ j ≤ ℓ - s`), (a) design (`ℓ - s < j < ℓ`, given by `Nd`). -/
noncomputable def blockNum (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
    (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F) (c : Fin s) (j : ℕ) : F[X] :=
  if j = 0 then
    C θ⁻¹ * (C (v c)⁻¹ * wPoly a ^ (ℓ - 1) * wCo a c ^ 2 +
      wPoly a ^ ℓ * ∑ n ∈ range (s - 1), C (Fd n c c) * Nd c (ℓ - 1 - n))
  else if j ≤ ℓ - s then C (v' c)⁻¹ * wPoly a ^ (ℓ - 1 - j) * wCo a c
  else Nd c j

/-- **Digit `d = ℓn + j` of coordinate `c`** of the block-periodic residue sequence (`def:block`):
`θ^{n+1} Res_{a_c}(V N_{c,j} / ((z - a_c)^{ℓ(n+1)} w_c^{ℓ(n+1)+1}) dz) = Res_{a_c}(V φ_{c,j} Ω^{-(n+1)} dz)`. -/
noncomputable def blockDig (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
    (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F) (c : Fin s) (d : ℕ) (V : F[X]) : F :=
  θ ^ (d / ℓ + 1) * locRes (a c) (ℓ * (d / ℓ + 1)) (V * blockNum a θ ℓ v Fd Nd v' c (d % ℓ))
    (wCo a c ^ (ℓ * (d / ℓ + 1) + 1))

/-- **The block-periodic residue sequence** (`def:block`): `C_c[d][k] = blockDig c d (z^k)`. -/
noncomputable def blockGen (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
    (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F) : Gen s F :=
  fun c d k => blockDig a θ ℓ v Fd Nd v' c d (X ^ k)

end Block

section Inst
variable {p : ℕ} [Fact p.Prime]

/-- The design of `thm:block`(a): `F_0 = ((-1, 1), (-1, -1))`. -/
def blk2F : ℕ → Fin 2 → Fin 2 → ℤ := fun _ => !![-1, 1; -1, -1]

/-- The design numerators of `thm:block`(a) (solutions of (a)): `N_{0,1} = 1`, `N_{1,1} = -1`. -/
noncomputable def blk2N : Fin 2 → ℕ → (ZMod p)[X] := fun c _ => if c = 0 then 1 else -1

/-- **`thm:block`(a)**: `s = ℓ = 2`, places `(0, 1)`, row constants `v = (1, 1)`, `F_0 = ((-1,1),(-1,-1))`. -/
noncomputable def blk2 (θ : ZMod p) : Gen 2 (ZMod p) :=
  blockGen faurePl θ 2 1 (blockF blk2F) blk2N 1

/-- The places `(0, 2, 1)` of `thm:block`(b). -/
def blk3a : Fin 3 → ZMod p := ![0, 2, 1]

/-- The layer `(M, J)` of `thm:block`(b) (the three-dimensional nets). -/
def blk3F : ℕ → Fin 3 → Fin 3 → ℤ := fun n =>
  if n = 0 then !![-1, -1, 1; 1, -1, -1; -1, 1, -1] else !![0, 0, -1; -1, 0, 0; 0, -1, 0]

/-- The row constants `v = (1/2, 1/2, -1)` of `thm:block`(b). -/
noncomputable def blk3v : Fin 3 → ZMod p := ![(2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, -1]

/-- The design numerators of `thm:block`(b) (solutions of (a)): `N_{c,2}` (`n = 0`) `= 2 - z, 2z - 2, 2z` and
`N_{c,1}` (`n = 1`) `= z, z - 2, 4z - 4` for `c = 0, 1, 2`. -/
noncomputable def blk3N : Fin 3 → ℕ → (ZMod p)[X] := fun c j =>
  if j = 2 then ![C 2 - X, C 2 * X - C 2, C 2 * X] c else ![X, X - C 2, C 4 * X - C 4] c

/-- **`thm:block`(b)**: `s = ℓ = 3`, places `(0, 2, 1)`, `v = (1/2, 1/2, -1)`, `(F_0, F_1) = (M, J)`. -/
noncomputable def blk3 (θ : ZMod p) : Gen 3 (ZMod p) :=
  blockGen blk3a θ 3 blk3v (blockF blk3F) blk3N 1

/-- The design of `cor:gauss`: `F_0 = ((-1, u), (-u, -1))`. -/
def gaussF (u : ℤ) : ℕ → Fin 2 → Fin 2 → ℤ := fun _ => !![-1, u; -u, -1]

/-- The design numerators of `cor:gauss`: `N_{0,1} = -1/u`, `N_{1,1} = 1/u²` (solutions of (a)). -/
noncomputable def gaussN {F : Type*} [Field F] (u : F) : Fin 2 → ℕ → F[X] :=
  fun c _ => if c = 0 then C (-u⁻¹) else C (u⁻¹ ^ 2)

/-- **`cor:gauss`**: `s = ℓ = 2`, places `(0, 1)`, `v = (-u, -1)`, `F_0 = ((-1,u),(-u,-1))` (`p = u² + 1`). -/
noncomputable def gaussGen (u : ℤ) (θ : ZMod p) : Gen 2 (ZMod p) :=
  blockGen faurePl θ 2 ![-(u : ZMod p), -1] (blockF (gaussF u)) (gaussN (u : ZMod p)) 1

/-- Decoding `{0,1,2} → {-1,0,1}` (for the exhaustive checks by `decide`). -/
def dec3 {s : ℕ} (e' : Fin s → Fin 3) : Fin s → ℤ := fun c => ((e' c : ℕ) : ℤ) - 1

/-- The changes `σ_i = ∑_c e_c F_0[i][c]` of `thm:block`(a) (integers). -/
def blk2sig (e : Fin 2 → ℤ) (i : Fin 2) : ℤ := ∑ c, e c * blk2F 0 i c

/-- The changes of `thm:block`(b): `σ_i = ∑_c e_c (M[i][c] + [l_c ≥ 2] J[i][c])` (integers; `ω_c = [l_c ≥ 2]`). -/
def blk3sig (e : Fin 3 → ℤ) (ω : Fin 3 → Bool) (i : Fin 3) : ℤ :=
  ∑ c, e c * (blk3F 0 i c + if ω c then blk3F 1 i c else 0)

/-- The changes of `cor:gauss`: `σ_i = ∑_c e_c F_0[i][c]` (integers). -/
def gsig (u : ℤ) (e : Fin 2 → ℤ) (i : Fin 2) : ℤ := ∑ c, e c * gaussF u 0 i c

end Inst

end GeoSeq
