/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs

@[expose] public section

/-!
# GeoSeq stage V6: definitions for `prop:P0`(c) and `thm:A` (`sec:antipode`, `app:LFdata`)

* **The limit hierarchy** (`sec:antipode`, before `prop:P0`), for the data of a staggered rule (`StagData`), rows in
  the stored order of every column (the paper sorts them by `|n|`): `stMu` = `μ_t = k|n_t| u` (the step of row `t`
  divided by `p` in the limit), `stLam` = `λ_t = 2ε_t` (the window fraction of its row), `stNbar` = `N̄_t`
  (`N̄_1 = 2 + (1 - λ_1)/μ_1`, `N̄_t = N̄_{t-1} + 1/μ_t`; rows from `0`), and `LimHier` = the limit hierarchy:
  `μ_1 < λ_1`, `N̄_{t-1} μ_t < λ_t` in every column, and the fixed depth-zero crosses strictly inside their
  windows (`u|n_{c←c'}| < ε_•` for `c ≠ c⋆`, `2u|n_{⋆←i}| < 2ε_{⋆←C}`).
* **The designs of `thm:A`** (proof of `thm:A`): `faureFr s` = the Faure places `(0, 1, …, s-1)`;
  `taDesign s R` = staggered coordinate `0`, natural order of `C = {1, …, s-1}`, `Q_r = R^r` (on coordinate `r`);
  `taRows s` = the row order of decreasing exponent (row `c` of column `c'` carries `R^{c-c'}`).
* **The factors of the proof of `thm:A`**: `taG` = the `R`-independent factor `G(c,c')` of the step of row `c` in
  column `c'` (`1` for the half-cell offsets, `n°_{cc'}` at `R = 1` otherwise), `taW` = `w(c,c') = k|G(c,c')|`,
  `taB` = a common bound `∑ (w + w⁻¹)`.
* **The designs of `tab:BSdata`, `s = 4, 5`**: `a4Design = taDesign 4 153` (`c⋆ = 0`, order `(1,2,3)`,
  `Q_r = 153^r`), `a4u`, `a4Data` (`δ = 2`, `L = 3 581 577`, `ε = 7/250`); `a5Design` (`c⋆ = 4`, order
  `(0,1,2,3)`, `Q_r = 99^r`), `a5Rows`, `a5u`, `a5Data` (`δ = 5`, `L = 96 059 601`, `ε = 23/1000`).
-/

namespace GeoSeq

open Finset

/-! ## The limit hierarchy (`sec:antipode`, before `prop:P0`) -/

section Hier

variable {K : Type*} [Field K] [LinearOrder K] {s : ℕ}

/-- `μ_t = k|n_t| u`: the step of row `t` (stored order, from `0`) of column `c'`, divided by `p`, in the limit
(`k = 1` in column `c⋆`, `k = 2` in a doubled column, where the half-cell offset contributes `2|n_{⋆←i}|`). -/
def stMu (D : StagData s) (c' : Fin s) (t : ℕ) : K := (stCoef D c' (D.rows c' t) : K) * (D.u : K)

/-- `λ_t = 2ε_t`, the window fraction of the row of step `t` of column `c'`. -/
def stLam (D : StagData s) (c' : Fin s) (t : ℕ) : K := 2 * (stFrac D c' (D.rows c' t) : K)

/-- `N̄_1 = 2 + (1 - λ_1)/μ_1`, `N̄_t = N̄_{t-1} + 1/μ_t` (rows from `0`). -/
def stNbar (D : StagData s) (c' : Fin s) : ℕ → K
  | 0 => 2 + (1 - stLam D c' 0) / stMu D c' 0
  | t + 1 => stNbar D c' t + 1 / stMu D c' (t + 1)

/-- **The limit hierarchy** (`sec:antipode`): in every column `μ_1 < λ_1` and `N̄_{t-1} μ_t < λ_t`
(`2 ≤ t ≤ s-1`), and the fixed depth-zero crosses lie strictly inside their windows: `u|n_{c←c'}| < ε_•` for
`c ≠ c⋆` (`ε_•` the fraction of `W_{c←c'}`) and `2u|n_{⋆←i}| < 2ε_{⋆←C}` (`nI c⋆ i = 2n_{⋆←i}`). -/
def LimHier (D : StagData s) : Prop :=
  (∀ c' : Fin s, stMu (K := K) D c' 0 < stLam D c' 0 ∧
    ∀ t < s - 2, stNbar (K := K) D c' t * stMu D c' (t + 1) < stLam D c' (t + 1)) ∧
  (∀ c c' : Fin s, c ≠ D.cs → c ≠ c' → (D.u : K) * ((D.nI c c').natAbs : K) < (stFrac D c' c : K)) ∧
  ∀ i : Fin s, i ≠ D.cs → (D.u : K) * ((D.nI D.cs i).natAbs : K) < 2 * (D.eSC : K)

end Hier

/-! ## The designs of `thm:A` -/

/-- The Faure places `(0, 1, …, s-1)` as an integer frame. -/
def faureFr (s : ℕ) : List ℤ := (List.range s).map (fun i : ℕ => (i : ℤ))

/-- **The design of the proof of `thm:A`**: Faure places, staggered coordinate `0`, the natural order
`(1, …, s-1)` of `C`, and `Q_r = R^r` on coordinate `r` (`Q 0` is not used). -/
def taDesign (s R : ℕ) [NeZero s] : StagDesign s := ⟨faureFr s, 0, fun j => (R : ℚ) ^ (j : ℕ)⟩

/-- The row order of decreasing exponent: column `c'` lists `s-1, s-2, …, 0` without `c'`
(row `c` of column `c'` carries the factor `R^{c-c'}`). -/
def taRows (s : ℕ) : Fin s → ℕ → Fin s := fun c' t =>
  if t + (c' : ℕ) + 1 < s then ⟨s - 1 - t, by have := c'.pos; omega⟩
  else ⟨s - 2 - t, by have := c'.pos; omega⟩

/-! ## The factors of the proof of `thm:A` -/

/-- The `R`-independent factor `G(c,c')`: `1` for the half-cell offsets (`c = c⋆ = 0`), else `n°_{cc'}` at `R = 1`. -/
def taG (s : ℕ) [NeZero s] (δ : ℕ) (c c' : Fin s) : ℚ := if c = 0 then 1 else sdN (taDesign s 1) δ 1 c c'

/-- `w(c,c') = k|G(c,c')|` with `k = 1` in column `c⋆` and for the half-cell offsets, `k = 2` otherwise. -/
def taW (s : ℕ) [NeZero s] (δ : ℕ) (c c' : Fin s) : ℚ := |taG s δ c c'| * (if c' = 0 ∨ c = 0 then 1 else 2)

/-- A crude common bound for `w` and `1/w`: `B = ∑_{c,c'} (w(c,c') + w(c,c')⁻¹)`. -/
def taB (s : ℕ) [NeZero s] (δ : ℕ) : ℚ := ∑ c : Fin s, ∑ c' : Fin s, (taW s δ c c' + (taW s δ c c')⁻¹)

/-! ## The designs of `tab:BSdata`, `s = 4, 5` -/

/-- The `s = 4` design of `tab:BSdata`: Faure places `(0,1,2,3)`, `c⋆ = 0`, order `(1,2,3)`, `Q_r = 153^r`. -/
def a4Design : StagDesign 4 := taDesign 4 153

/-- `u = 259/(1.1730858534·10^16)` (`tab:BSdata`, `s = 4`). -/
def a4u : ℚ := 259 / 11730858534000000

/-- The data of the staggered rule of the `s = 4` design (`δ = 2`, `L = 3 581 577`, uniform `ε = 7/250`, rows of
decreasing `|n|`). -/
def a4Data : StagData 4 := sdData a4Design 2 3581577 (taRows 4) (7 / 250) (7 / 250) (7 / 250) a4u

/-- The `s = 5` design of `tab:BSdata`: Faure places `(0,…,4)`, `c⋆ = 4`, order `(0,1,2,3)`, `Q_r = 99^r`
(`Q` on coordinate `j` is `99^{j+1}`; `Q 4` is not used). -/
def a5Design : StagDesign 5 := ⟨faureFr 5, 4, fun j => (99 : ℚ) ^ ((j : ℕ) + 1)⟩

/-- The row orders of the `s = 5` design (`|n|` decreasing): columns `0..3` list the other coordinates of `C` in
decreasing order and then `c⋆ = 4`; column `4` lists `3, 2, 1, 0`. -/
def a5Rows : Fin 5 → ℕ → Fin 5 := fun c' t =>
  Fin.ofNat 5 ((([[3, 2, 1, 4], [3, 2, 0, 4], [3, 1, 0, 4], [2, 1, 0, 4], [3, 2, 1, 0]] : List (List ℕ)).getD c' []).getD
    t 0)

/-- `u = 851/(4.860548184640896·10^21)` (`tab:BSdata`, `s = 5`). -/
def a5u : ℚ := 851 / 4860548184640896000000

/-- The data of the staggered rule of the `s = 5` design (`δ = 5`, `L = 96 059 601`, uniform `ε = 23/1000`). -/
def a5Data : StagData 5 := sdData a5Design 5 96059601 a5Rows (23 / 1000) (23 / 1000) (23 / 1000) a5u

end GeoSeq
