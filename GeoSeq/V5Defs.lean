/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-!
# GeoSeq stage V5: definitions for the staggered design (`sec:antipode`, `app:LFdata`)

* **Continuum windows** (`thm:BS`): subsets of `ℝ` standing for subsets of `ℝ/ℤ` (`f̄` is `1`-periodic, so
  representatives suffice); `ctsSumset` = `S_c(e)`, `CtsLB W LB` = "`LB ≤ c*(W)`" in pointwise form (as `WinLB`);
  `stagCts` = the staggered continuum windows; `epsS` = `ε_s`.
* **Staggered windows at a prime** (`lem:W`): `halfZ p = (p+1)/2` (the residue `½`); `stagWin` = the windows
  (own windows of `C` and `c⋆`, half-cell offsets, crosses), with `Mv cs = M⋆` and `Mv i = M_i`;
  the three numbers `wTst = T⋆`, `wTCs = T_{C⋆}`, `wT2 = T_2` and `lbW` = `LB_W`.
* **Staggered designs** (`lem:R`, integer frames): `StagDesign` = integer places (`frameA`), staggered
  coordinate, rationals `Q` indexed by the coordinates of `C` (the paper's `Q_r` sits at `j_r`);
  `sdDelta` = `Δ_{cc'} = w'(a_{c'})(a_{c'}-a_c)`, `sdG` = the constants `g_c`, `sdN` = `n_{cc'}`, `sdKap` = the
  rational cross `θ g_c/(g_{c'} Δ_{cc'})`; `sdDeltaOK` (the conditions defining `δ`), `sdLOK` (the conditions
  defining `L`), `sdOK` (distinct places, `Q > 0` with odd numerator and denominator).
* **Staggered rule** (`def:BS`, `prop:P0`), abstract data `StagData`: staggered coordinate, the integers
  `nI c c' = n_{cc'}` (`c ≠ c⋆`) and `nI c⋆ i = 2 n_{⋆←i} = L/Q_i` (odd), the row order of every column (as
  used by `lem:ws`), the window fractions and `u`. The predicate `StP` = `𝒫(p)` ((P1)–(P6) of `app:LFdata`),
  over any ordered field (`ℚ` for exact evaluation, `ℝ` for the theorems), with `stNP` = `N_t^+`,
  `stMstP` = `M⋆^+`, `stMP` = `M^+`. The integers of the rule at a prime `p`: `stT` = `T` (S1), `stB` = the
  half-widths (S2), `stN`/`stMv` = `M⋆`, `M_i` (S3), `stWin` = its windows; `sdTheta`, `sdLam` = `θ = 2^δ L T` and
  `λ_c = g_c w'(a_c)` in `𝔽_p`, `sdData` = the rule data of a staggered design (`lem:R`).
* **The design of `thm:A3`** (`tab:BSdata`, `s = 3`): `a3Design` (places `(0,1,2)`, `c⋆ = 0`, `Q = (7, 3)` on the
  coordinates `1, 2`), `a3Rows` (rows sorted by `|n|`), `a3u` (`u = 891/78 400 000`), `a3Data` (`δ = 2`, `L = 21`,
  fractions `(27/1000, 1/200, 1/10)`).
-/

namespace GeoSeq

open Finset

/-! ## Continuum windows (`thm:BS`) -/

section Cts

variable {s : ℕ}

/-- **The continuum sumset** `S_c(e) = ∑_{c' : e_{c'} ≠ 0} e_{c'} W_{c←c'}` (`sec:antipode`, from `sec:steer`), for
windows given by sets of real representatives. -/
def ctsSumset (W : Fin s → Fin s → Set ℝ) (e : Fin s → ℤ) (c : Fin s) : Set ℝ :=
  {Φ | ∃ x : Fin s → ℝ, (∀ c', e c' ≠ 0 → x c' ∈ W c c') ∧ Φ = ∑ c', (e c' : ℝ) * x c'}

/-- **`LB ≤ c*(W)`**, the continuum bound `c*(W)² = min_e ∑_c inf_{Φ ∈ S_c(e)} f̄(e_c, Φ)²` (`sec:antipode`), in
pointwise form: for every step `e ∈ {-1,0,1}^s \ {0}` and every choice `Φ_c ∈ S_c(e)`,
`LB ≤ (∑_c f̄(e_c, Φ_c)²)^{1/2}` (`f̄` is `1`-periodic, so real representatives of `ℝ/ℤ` suffice). -/
def CtsLB (W : Fin s → Fin s → Set ℝ) (LB : ℝ) : Prop :=
  ∀ e : Fin s → ℤ, (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
    ∀ Φ : Fin s → ℝ, (∀ c, Φ c ∈ ctsSumset W e c) → LB ≤ Real.sqrt (∑ c, fbar (e c) (Φ c) ^ 2)

/-- **The staggered (continuum) windows** (`sec:antipode`), staggered coordinate `cs = c⋆`: column `i ≠ c⋆` has
own window `{-a}`, cross into `c⋆` `½ + [-ε, ε]` and crosses `[-ε, ε]` into the other coordinates; column `c⋆`
has own window `{0}` and crosses `[-ε, ε]`. (`W c c'` = `W_{c←c'}`.) -/
def stagCts (cs : Fin s) (a ε : ℝ) : Fin s → Fin s → Set ℝ := fun c c' =>
  if c' = cs then (if c = cs then {0} else Set.Icc (-ε) ε)
  else if c = c' then {-a}
  else if c = cs then Set.Icc (1 / 2 - ε) (1 / 2 + ε)
  else Set.Icc (-ε) ε

end Cts

/-- `ε_s = (2s + 1 - √(3s² + 4s))/(2(s² + 1))` (`thm:BS`). -/
noncomputable def epsS (s : ℕ) : ℝ :=
  (2 * s + 1 - Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s)) / (2 * ((s : ℝ) ^ 2 + 1))

/-! ## Staggered windows at a prime (`lem:W`) -/

/-- The residue `½ = (p+1)/2` (`sec:antipode`), as an integer. -/
def halfZ (p : ℕ) : ℤ := ((p : ℤ) + 1) / 2

section Win

variable {s : ℕ}

/-- **The staggered windows at `p`** (`sec:antipode`, before `lem:W`), staggered coordinate `cs = c⋆`, `C` the
other coordinates; `Mv cs = M⋆`, `Mv i = M_i` (`i ∈ C`), `Bcc = B_{C←C}`, `Bsc = B_{⋆←C}`, `Bcs = B_{C←⋆}`:
column `i ∈ C`: own `[-(A+M_i-1), -A]`, `W_{⋆←i} = ½ + [-B_{⋆←C}, B_{⋆←C}]`, `W_{j←i} = [-B_{C←C}, B_{C←C}]`;
column `c⋆`: own `[-(M⋆-1), 0]`, `W_{j←⋆} = [-B_{C←⋆}, B_{C←⋆}]`. (`W c c'` = `W_{c←c'}`.) -/
def stagWin (p : ℕ) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ) :
    Fin s → Fin s → Set (ZMod p) := fun c c' =>
  if c' = cs then
    (if c = cs then intWin p (-((Mv cs : ℤ) - 1)) 0 else intWin p (-(Bcs : ℤ)) Bcs)
  else if c = c' then intWin p (-((A : ℤ) + Mv c' - 1)) (-(A : ℤ))
  else if c = cs then intWin p (halfZ p - Bsc) (halfZ p + Bsc)
  else intWin p (-(Bcc : ℤ)) Bcc

end Win

/-- `T⋆ = (1 - M⋆/p)²` (`lem:W`). -/
noncomputable def wTst (p Mst : ℕ) : ℝ := (1 - (Mst : ℝ) / p) ^ 2

/-- `T_{C⋆} = (1 - (A+M+B_{C←⋆})/p)² + ((p - 1 - 2B_{⋆←C} - 2M⋆)/(2p))²` (`lem:W`). -/
noncomputable def wTCs (p A M Mst Bsc Bcs : ℕ) : ℝ :=
  (1 - ((A : ℝ) + M + Bcs) / p) ^ 2 + (((p : ℝ) - 1 - 2 * Bsc - 2 * Mst) / (2 * p)) ^ 2

/-- `T_2 = 2(1 - (A+M+(s-2)B_{C←C}+B_{C←⋆})/p)²` (`lem:W`). -/
noncomputable def wT2 (p s A M Bcc Bcs : ℕ) : ℝ :=
  2 * (1 - ((A : ℝ) + M + ((s - 2 : ℕ) : ℝ) * Bcc + Bcs) / p) ^ 2

/-- **`LB_W`** (`lem:W`): `LB_W² = min(T⋆, T_{C⋆}, T_2)`, `T_2` omitted for `s = 2`. -/
noncomputable def lbW (p s A M Mst Bcc Bsc Bcs : ℕ) : ℝ :=
  Real.sqrt (if 3 ≤ s then min (min (wTst p Mst) (wTCs p A M Mst Bsc Bcs)) (wT2 p s A M Bcc Bcs)
    else min (wTst p Mst) (wTCs p A M Mst Bsc Bcs))

/-! ## Staggered designs (`lem:R`) -/

/-- **A staggered design over an integer frame** (`sec:antipode`, before `lem:R`): places `a_c = frameA fr c`,
staggered coordinate `cs = c⋆`, and the positive rationals `Q c` for the coordinates `c ∈ C` (the paper's
`Q_r` attached to the `r`-th coordinate `j_r` of the order of `C`; `Q cs` is not used). -/
structure StagDesign (s : ℕ) where
  fr : List ℤ
  cs : Fin s
  Q : Fin s → ℚ

section Design

variable {s : ℕ}

/-- `Δ_{cc'} = w'(a_{c'}) (a_{c'} - a_c)` (`sec:antipode`), an integer for an integer frame. -/
def sdDelta (D : StagDesign s) (c c' : Fin s) : ℤ :=
  frameW s D.fr c' * (frameA D.fr c' - frameA D.fr c)

/-- The constants of `lem:R`: `g_{c⋆} = 1`, `g_j = 2^{1+δ} Q_j/Δ_{⋆j}` (`j ∈ C`). -/
def sdG (D : StagDesign s) (δ : ℕ) (c : Fin s) : ℚ :=
  if c = D.cs then 1 else 2 ^ (1 + δ) * D.Q c / (sdDelta D D.cs c : ℚ)

/-- **The rationals `n_{cc'}` of `lem:R`**: `n_{⋆←j} = L/(2Q_j)`, `n_{j←⋆} = 2^{1+2δ} L Q_j/(Δ_{j⋆}Δ_{⋆j})`,
`n_{j←j'} = 2^δ L (Q_j/Q_{j'}) Δ_{⋆j'}/(Δ_{⋆j} Δ_{jj'})` (`j, j' ∈ C`; row `c`, column `c'`). -/
def sdN (D : StagDesign s) (δ L : ℕ) (c c' : Fin s) : ℚ :=
  if c = D.cs then (L : ℚ) / (2 * D.Q c')
  else if c' = D.cs then 2 ^ (1 + 2 * δ) * L * D.Q c / ((sdDelta D c D.cs : ℚ) * sdDelta D D.cs c)
  else 2 ^ δ * L * (D.Q c / D.Q c') * ((sdDelta D D.cs c' : ℚ) / ((sdDelta D D.cs c : ℚ) * sdDelta D c c'))

/-- The depth-zero cross in the form of `prop:LI`(c) with the constants `g_c`:
`κ_{c←c'} = θ g_c/(g_{c'} Δ_{cc'})` (rational). -/
def sdKap (D : StagDesign s) (δ : ℕ) (θ : ℚ) (c c' : Fin s) : ℚ :=
  θ * sdG D δ c / (sdG D δ c' * sdDelta D c c')

/-- **The conditions defining `δ`** (`sec:antipode`, before `lem:R`): `1 + 2δ ≥ v_2(Δ_{j⋆}Δ_{⋆j})` for every
`j ∈ C`, and `δ + v_2(Δ_{⋆j'}) - v_2(Δ_{⋆j}) - v_2(Δ_{jj'}) ≥ 0` for all `j ≠ j'` in `C`. -/
def sdDeltaOK (D : StagDesign s) (δ : ℕ) : Prop :=
  (∀ j : Fin s, j ≠ D.cs → padicValInt 2 (sdDelta D j D.cs * sdDelta D D.cs j) ≤ 1 + 2 * δ) ∧
  ∀ j j' : Fin s, j ≠ D.cs → j' ≠ D.cs → j ≠ j' →
    padicValInt 2 (sdDelta D D.cs j) + padicValInt 2 (sdDelta D j j') ≤ δ + padicValInt 2 (sdDelta D D.cs j')

/-- **The conditions defining `L`** (`sec:antipode`, before `lem:R`, the corrected definition): `L` is odd,
every `L/Q_j` is an integer, and every `L n°_{cc'}` (`c ≠ c⋆`) is an integer, `n°` = `n` at `L = 1`. -/
def sdLOK (D : StagDesign s) (δ L : ℕ) : Prop :=
  L % 2 = 1 ∧ (∀ j : Fin s, j ≠ D.cs → ((L : ℚ) / D.Q j).den = 1) ∧
    ∀ c c' : Fin s, c ≠ D.cs → c ≠ c' → ((L : ℚ) * sdN D δ 1 c c').den = 1

/-- A staggered design: distinct places, and `Q_j > 0` with odd numerator and odd denominator (`j ∈ C`). -/
def sdOK (D : StagDesign s) : Prop :=
  (∀ b c : Fin s, b ≠ c → frameA D.fr b ≠ frameA D.fr c) ∧
    ∀ j : Fin s, j ≠ D.cs → 0 < D.Q j ∧ (D.Q j).num % 2 = 1 ∧ (D.Q j).den % 2 = 1

/-- (S1) the scale `θ = 2^δ L T` in `𝔽_p` (`lem:R`). -/
def sdTheta (p δ L T : ℕ) : ZMod p := ((2 ^ δ * L * T : ℕ) : ZMod p)

/-- The constants `λ_c = g_c w'(a_c)` in `𝔽_p` of the multipliers with constant terms `g_c` (`prop:LI`(a),
`λ`-form; `g_c` the rationals of `lem:R`, reduced mod `p`). -/
def sdLam (D : StagDesign s) (p δ : ℕ) [Fact p.Prime] : Fin s → ZMod p :=
  fun c => ((sdG D δ c : ℚ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p)

end Design

/-! ## The staggered rule and the predicate `𝒫(p)` (`def:BS`, `prop:P0`) -/

/-- **Data of a staggered rule** (`def:BS`, `app:LFdata`): staggered coordinate `cs = c⋆`; integers `nI c c'`
with `nI c c' = n_{cc'}` for `c ≠ c⋆` and `nI c⋆ i = 2 n_{⋆←i} = L/Q_i` (an odd integer, `lem:R`); the row order
`rows c' 0, …, rows c' (s-2)` of every column (the order of `lem:ws`, fast row first; the paper sorts by `|n|`);
the window fractions `ε_{C←⋆}`, `ε_{C←C}`, `ε_{⋆←C}` and `u`. -/
structure StagData (s : ℕ) where
  cs : Fin s
  nI : Fin s → Fin s → ℤ
  rows : Fin s → ℕ → Fin s
  eCS : ℚ
  eCC : ℚ
  eSC : ℚ
  u : ℚ

section Rule

variable {s : ℕ}

/-- Validity of the data: every column lists each other row exactly among its `s - 1` rows (and never
itself), all crosses are nonzero, and the half-cell numbers `nI c⋆ i` are odd. Decidable. -/
def StagData.Valid (D : StagData s) : Prop :=
  (∀ c' : Fin s, ∀ t < s - 1, D.rows c' t ≠ c') ∧
  (∀ c' c : Fin s, c ≠ c' → c ∈ (List.range (s - 1)).map (D.rows c')) ∧
  (∀ c c' : Fin s, c ≠ c' → D.nI c c' ≠ 0) ∧
  ∀ i : Fin s, i ≠ D.cs → D.nI D.cs i % 2 = 1

/-- The window fraction of `W_{r←c'}`: `ε_{C←⋆}` in column `c⋆`, `ε_{⋆←C}` for the half-cell offsets,
`ε_{C←C}` otherwise. -/
def stFrac (D : StagData s) (c' r : Fin s) : ℚ :=
  if c' = D.cs then D.eCS else if r = D.cs then D.eSC else D.eCC

/-- The step of row `r` in column `c'` divided by `T`: `k|n_{r c'}|` with `k = 1` in column `c⋆` and `k = 2` in a
doubled column (where the half-cell offset contributes `2|n_{⋆←i}| = |nI c⋆ i|`). -/
def stCoef (D : StagData s) (c' r : Fin s) : ℕ :=
  if c' = D.cs ∨ r = D.cs then (D.nI r c').natAbs else 2 * (D.nI r c').natAbs

/-- `x = 1 - (s-2)ε_{C←C} - 2ε_{C←⋆}` (`prop:P0`). -/
def stX (D : StagData s) : ℚ := 1 - ((s - 2 : ℕ) : ℚ) * D.eCC - 2 * D.eCS

/-- `y = ½ - ε_{⋆←C}` (`prop:P0`). -/
def stY (D : StagData s) : ℚ := 1 / 2 - D.eSC

section Field

variable {K : Type*} [Field K] [LinearOrder K]

/-- `ν_t^- = k|n_t|(up - 2)` (`app:LFdata`; rows of column `c'` in the stored order, from `0`). -/
def stNuM (D : StagData s) (p : K) (c' : Fin s) (t : ℕ) : K :=
  (stCoef D c' (D.rows c' t) : K) * ((D.u : K) * p - 2)

/-- `ν_t^+ = k|n_t| up`. -/
def stNuP (D : StagData s) (p : K) (c' : Fin s) (t : ℕ) : K :=
  (stCoef D c' (D.rows c' t) : K) * ((D.u : K) * p)

/-- `ℓ_t = 2ε_t p - 1`. -/
def stEll (D : StagData s) (p : K) (c' : Fin s) (t : ℕ) : K :=
  2 * (stFrac D c' (D.rows c' t) : K) * p - 1

/-- `N_1^+ = 2 + max(0, (p - ℓ_1)/ν_1^-)`, `N_t^+ = N_{t-1}^+ + p/ν_t^-` (rows from `0`). -/
def stNP (D : StagData s) (p : K) (c' : Fin s) : ℕ → K
  | 0 => 2 + max 0 ((p - stEll D p c' 0) / stNuM D p c' 0)
  | t + 1 => stNP D p c' t + p / stNuM D p c' (t + 1)

/-- `M⋆^+ = N_{s-1}^+` of column `c⋆`. -/
def stMstP (D : StagData s) (p : K) : K := stNP D p D.cs (s - 2)

/-- `M^+ = max_{i ∈ C} (2N_{s-1}^+ - 1)` (as a fold, starting from `0`; all terms are `≥ 3` under `𝒫`). -/
def stMP (D : StagData s) (p : K) : K :=
  (List.finRange s).foldr (fun c m => if c = D.cs then m else max (2 * stNP D p c (s - 2) - 1) m) 0

/-- `z = 1 - 2(s-2)ε_{C←C} - 2ε_{C←⋆} - M^+/p` (`(P5)`). -/
def stZ (D : StagData s) (p : K) : K :=
  1 - 2 * ((s - 2 : ℕ) : K) * (D.eCC : K) - 2 * (D.eCS : K) - stMP D p / p

/-- **The predicate `𝒫(p)`** (`app:LFdata`, (P1)–(P6)): rational functions of `p` over an ordered field. -/
def StP (D : StagData s) (p : K) : Prop :=
  -- (P1)
  2 < (D.u : K) * p ∧
  -- (P2)
  (∀ c' : Fin s, stNuP D p c' 0 ≤ stEll D p c' 0 ∧
    ∀ t < s - 2, stNP D p c' t * stNuP D p c' (t + 1) ≤ stEll D p c' (t + 1)) ∧
  -- (P3)
  (∀ c c' : Fin s, c ≠ D.cs → c ≠ c' →
    ((D.nI c c').natAbs : K) * ((D.u : K) * p) ≤ (stFrac D c' c : K) * p - 1) ∧
  (∀ i : Fin s, i ≠ D.cs → ((D.nI D.cs i).natAbs : K) * ((D.u : K) * p) ≤ 2 * ((D.eSC : K) * p - 1) - 1) ∧
  -- (P4)
  (1 < (stX D : K) ^ 2 + (stY D : K) ^ 2 ∧
    2 * (stX D : K) * stMP D p + 2 * (stY D : K) * (stMstP D p + 1 / 2) ≤
      p * ((stX D : K) ^ 2 + (stY D : K) ^ 2 - 1)) ∧
  -- (P5)
  (0 ≤ stZ D p ∧ 1 ≤ 2 * stZ D p ^ 2) ∧
  -- (P6)
  ((2 * ((s - 2 : ℕ) : K) * (D.eCC : K) + 2 * (D.eCS : K)) * p + stMP D p + 2 ≤ p - 1 ∧
    2 * (D.eSC : K) * p + 2 * stMstP D p + 2 < p - 1 ∧ stMP D p / p < (stX D : K))

end Field

/-- (S1) `T` = the largest odd integer `≤ ⌊up⌋`. -/
def stT (u : ℚ) (p : ℕ) : ℕ := if ⌊u * p⌋₊ % 2 = 1 then ⌊u * p⌋₊ else ⌊u * p⌋₊ - 1

/-- (S2) the half-width `B = ⌊εp⌋`. -/
def stB (e : ℚ) (p : ℕ) : ℕ := ⌊e * p⌋₊

/-- The half-width of `W_{r←c'}`. -/
def stBr (D : StagData s) (p : ℕ) (c' r : Fin s) : ℕ := stB (stFrac D c' r) p

/-- The arc length `2B + 1` of row `t` of column `c'`. -/
def stLen (D : StagData s) (p : ℕ) (c' : Fin s) (t : ℕ) : ℕ := 2 * stBr D p c' (D.rows c' t) + 1

/-- The step `|κ|` (column `c⋆`) or `|2κ|` (doubled column) of row `t` of column `c'`: `T k|n|`. -/
def stNu (D : StagData s) (p : ℕ) (c' : Fin s) (t : ℕ) : ℕ := stT D.u p * stCoef D c' (D.rows c' t)

/-- The number `N` of `lem:ws` for column `c'` (steps in the stored order, arcs of the rows). -/
def stN (D : StagData s) (p : ℕ) (c' : Fin s) : ℕ := wsN p (stLen D p c') (stNu D p c') (s - 2)

/-- (S3) `M⋆ = N` (column `c⋆`), `M_i = 2N^{(i)} - 1` (doubled column `i`). -/
def stMv (D : StagData s) (p : ℕ) (c' : Fin s) : ℕ := if c' = D.cs then stN D p c' else 2 * stN D p c' - 1

/-- `A = (s-2)B_{C←C} + B_{C←⋆}` (S2). -/
def stA (D : StagData s) (p : ℕ) : ℕ := (s - 2) * stB D.eCC p + stB D.eCS p

/-- `M = max_{i ∈ C} M_i`. -/
def stM (D : StagData s) (p : ℕ) : ℕ := (univ.erase D.cs).sup (stMv D p)

/-- **The windows of the staggered rule** at `p` ((S2), (S3)). -/
def stWin (D : StagData s) (p : ℕ) : Fin s → Fin s → Set (ZMod p) :=
  stagWin p D.cs (stA D p) (stMv D p) (stB D.eCC p) (stB D.eSC p) (stB D.eCS p)

instance (D : StagData s) : Decidable D.Valid := by unfold StagData.Valid; infer_instance

instance (D : StagData s) (p : ℚ) : Decidable (StP D p) := by unfold StP; infer_instance

/-- The data of the staggered rule of a staggered design (`lem:R`): `nI c c' = n_{cc'}` (`c ≠ c⋆`, an integer)
and `nI c⋆ j = L/Q_j` (an odd integer), with the given row orders, window fractions and `u`. -/
def sdData (D : StagDesign s) (δ L : ℕ) (rows : Fin s → ℕ → Fin s) (eCS eCC eSC u : ℚ) : StagData s :=
  ⟨D.cs, fun c c' => if c = D.cs then ((L : ℚ) / D.Q c').num else (sdN D δ L c c').num, rows, eCS, eCC, eSC, u⟩

end Rule

/-! ## The design of `thm:A3` (`tab:BSdata`, column `s = 3`) -/

/-- The design of `thm:A3`: places `(0,1,2)`, `c⋆ = 0`, `Q_1 = 7` (coordinate `1`), `Q_2 = 3` (coordinate `2`). -/
def a3Design : StagDesign 3 := ⟨[0, 1, 2], 0, fun c => if c = 1 then 7 else if c = 2 then 3 else 1⟩

/-- The row orders (`|n|` decreasing): column `0`: `(1, 2)`; column `1`: `(2, 0)`; column `2`: `(1, 0)`. -/
def a3Rows : Fin 3 → ℕ → Fin 3 := fun c t =>
  if c = 0 then (if t = 0 then 1 else 2) else if c = 1 then (if t = 0 then 2 else 0) else (if t = 0 then 1 else 0)

/-- `u = 891/78 400 000`. -/
def a3u : ℚ := 891 / 78400000

/-- The data of the staggered rule of `thm:A3` (`δ = 2`, `L = 21`, fractions `(27/1000, 1/200, 1/10)`). -/
def a3Data : StagData 3 := sdData a3Design 2 21 a3Rows (27 / 1000) (1 / 200) (1 / 10) a3u

end GeoSeq
