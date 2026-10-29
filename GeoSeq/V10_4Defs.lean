/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1SignDefs
public import Z3Net.ThmAMain

@[expose] public section

/-!
# GeoSeq stage V10-4 (paper V4, `thm:block`(c) for every `s`): definitions

Shared by the statement file `GeoSeq/Statements/V10_4.lean` and the proof files `GeoSeq/V10_4*.lean`
(the formalization notes of the research repository, stage V10-4).

* **Reachability** (`def:block`, the display before it): `IsReachable a v Fd γ` — for every column `c` and carry
  depth `n ≤ s - 2`, `F_n[i][c] = v_i⁻¹ τ_{ic} γ_{c,n}(τ_{ic})` (`i ≠ c`), `τ_{ic} = 1/(a_i - a_c)` (`tauF`), with a
  polynomial `γ_{c,n}` of exact degree `n`; the diagonal is not constrained.
* **Identity (a)** of `def:block` for one column, as a property of the design numerators `N_n = w_c φ_{c,s-1-n}`
  (`IdA`; the polynomial form used by `blockGen`, `u_i = wCoCo a c i / w_c`).
* **The design of `thm:block`(c) for every `s`**: the design `U*_s` of the nets (`Z3NetA.UstarF s`, the formal
  `def:Ustar` of the companion library `Z3Net/`, coordinate `0` at the place `∞`, coordinate `c ≥ 1` at the place
  `c - 1`) moved by `x ↦ 1/(x+1)` to the places `a_c = 1/c` (`a_0 = 0`; `ustarA`), with the row constants
  `v = (1, 1, 2, …, s-1)` (`ustarV`). Its design numerators (the unique solution of (a), `ustarNd`) are chosen by
  `Classical.epsilon`; `blkS` is the sequence.
* **The free diagonal** (V10-1, the research notes item 1): `ustarDiagF s δ` keeps the off-diagonal entries of
  `U*_s` and puts `F_0[c][c] = -δ_c` (deeper diagonal `0`); `blkSd` is its sequence (the numerators do not depend on
  the diagonal).
-/

namespace GeoSeq

open Finset Polynomial

section Reach
variable {F : Type*} [Field F] {s : ℕ}

/-- `τ_{ic} = 1/(a_i - a_c)` (`def:block`). -/
def tauF (a : Fin s → F) (i c : Fin s) : F := (a i - a c)⁻¹

/-- **Reachability** of a design (`def:block`): for every column `c` and depth `n ≤ s - 2`,
`F_n[i][c] = v_i⁻¹ τ_{ic} γ_{c,n}(τ_{ic})` for `i ≠ c`, with `γ_{c,n}` of exact degree `n`. -/
def IsReachable (a : Fin s → F) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) : Prop :=
  (∀ c n, n + 2 ≤ s → (γ c n).natDegree = n ∧ γ c n ≠ 0) ∧
    ∀ c i, i ≠ c → ∀ n, n + 2 ≤ s → Fd n i c = (v i)⁻¹ * tauF a i c * (γ c n).eval (tauF a i c)

/-- **Identity (a)** of `def:block` for the column `c`, in numerator form: `N n = w_c φ_{c,s-1-n}` and
`u_i = wCoCo a c i / w_c`, so (a) reads `wCoCo a c i = -v_i ∑_n F_n[i][c] N_n` (`i ≠ c`). -/
def IdA (a : Fin s → F) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F) (c : Fin s) (N : ℕ → F[X]) : Prop :=
  ∀ i, i ≠ c → wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * N n

open Classical in
/-- **The design numerators of `def:block`(a)** for a design `Fd` (generic): `designNd a v Fd c j = N_{s-1-j}`, `N` a
solution of identity (a) for the column `c` (`Classical.choose`; unique by `designNum_unique`); junk `0` if there is
none. -/
noncomputable def designNd (a : Fin s → F) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F) : Fin s → ℕ → F[X] :=
  fun c j => (if h : ∃ N : ℕ → F[X], IdA a v Fd c N then Classical.choose h else fun _ => 0) (s - 1 - j)

end Reach

section Ustar
variable {p : ℕ} [Fact p.Prime]

/-- The places `0, 1, 1/2, …, 1/(s-1)` of `thm:block`(c): `a_c = 1/c` (`a_0 = 0⁻¹ = 0`), the images of the nets'
places `∞, 0, 1, …, s-2` under `x ↦ 1/(x+1)`. -/
def ustarA (s : ℕ) : Fin s → ZMod p := fun c => ((c : ℕ) : ZMod p)⁻¹

/-- The row constants `v = (1, 1, 2, …, s-1)` of `thm:block`(c). -/
def ustarV (s : ℕ) : Fin s → ZMod p := fun c => if (c : ℕ) = 0 then 1 else ((c : ℕ) : ZMod p)

/-- `ς_c`: `1/c` for `c ≥ 1` (`= 1/(â_c+1)`), `-1` for the place `∞` (`c = 0`). -/
def sgC {s : ℕ} (c : Fin s) : ZMod p := if (c : ℕ) = 0 then -1 else ((c : ℕ) : ZMod p)⁻¹

/-- `A_c(X) = -X/c² - 1/c` for `c ≥ 1`, `A_∞(X) = X - 1`. -/
noncomputable def affC {s : ℕ} (c : Fin s) : (ZMod p)[X] :=
  if (c : ℕ) = 0 then X - C 1 else C (-(((c : ℕ) : ZMod p) ^ 2)⁻¹) * X + C (-((c : ℕ) : ZMod p)⁻¹)


/-- The weights `w_{ic}` of the nets (`Z3NetF.wN`, places `∞ = coordinate 0`, `c - 1`), reduced modulo `p`. -/
def wNp {s : ℕ} (i c : Fin s) : ZMod p :=
  if (i : ℕ) = 0 ∨ (c : ℕ) = 0 then 1 else (((i : ℕ) : ZMod p) - ((c : ℕ) : ZMod p))⁻¹

/-- The nodes `y_{ic}` of the nets (`Z3NetF.yN`), reduced modulo `p`. -/
def yNp {s : ℕ} (i c : Fin s) : ZMod p :=
  if (i : ℕ) = 0 then 0 else if (c : ℕ) = 0 then ((i : ℕ) : ZMod p) - 1
  else (((i : ℕ) : ZMod p) - ((c : ℕ) : ZMod p))⁻¹

/-- The design `U*_s` of `thm:block`(c), read in `ℤ/pℤ`. -/
noncomputable def ustarFd (s : ℕ) [NeZero s] : ℕ → Fin s → Fin s → ZMod p := blockF (Z3NetA.UstarF s)

/-- **The design numerators of `thm:block`(c)** (the unique solution of identity (a) of `def:block`, `ustar_hrel`,
`ustar_Nd_unique`): `ustarNd s c j = N_{s-1-j}` for the column `c` (it exists for every prime `p ≥ s`). -/
noncomputable def ustarNd (s : ℕ) [NeZero s] : Fin s → ℕ → (ZMod p)[X] :=
  designNd (ustarA s) (ustarV s) (ustarFd s)

/-- **`thm:block`(c) for every `s`**: the block-periodic residue sequence with `ℓ = s`, places `0, 1, 1/2, …, 1/(s-1)`,
row constants `(1, 1, 2, …, s-1)` and the design `U*_s` of the nets. -/
noncomputable def blkS (s : ℕ) [NeZero s] (θ : ZMod p) : Gen s (ZMod p) :=
  blockGen (ustarA s) θ s (ustarV s) (ustarFd s) (ustarNd s) 1

/-- The design `U*_s` with the free diagonal: off the diagonal `U*_s`, `F_0[c][c] = -δ_c`, deeper diagonal `0`. -/
noncomputable def ustarDiagF (s : ℕ) [NeZero s] (δ : Fin s → ℤ) : ℕ → Fin s → Fin s → ℤ :=
  fun n i c => if i = c then (if n = 0 then -δ c else 0) else Z3NetA.UstarF s n i c

/-- **The block-periodic sequence with the free diagonal `δ`** (same places, row constants and numerators as
`blkS`; identity (a) does not involve the diagonal). -/
noncomputable def blkSd (s : ℕ) [NeZero s] (δ : Fin s → ℤ) (θ : ZMod p) : Gen s (ZMod p) :=
  blockGen (ustarA s) θ s (ustarV s) (blockF (ustarDiagF s δ)) (ustarNd s) 1

end Ustar

end GeoSeq
