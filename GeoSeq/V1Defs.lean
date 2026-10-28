/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V0Defs

@[expose] public section

/-!
# GeoSeq stage V1: definitions for the general window machinery (`sec:steer`, `prop:steer`)

Setting of `sec:steer` (V3 paper): a frame `(a_0, …, a_{s-1}; ∞)` given by its scaled local roots
`zθ c = z_c(θx)` (places `a_c = ssPlace zθ c`, `w'(a_c) = placeDer zθ c`), a scale `θ`, and constants
`λ_c` (`lamv c`; `prop:LI`(a), normalisation `ϖ̂ = 1`). Everything is indexed by `Fin s`, any `s`.

* `kapL` = the depth-zero cross `κ_{c←c'} = θ λ_c/(λ_{c'} w'(a_c) (a_{c'} - a_c))` (`prop:LI`(c), λ-form);
  `stAlpha` = the depth direction `α_{c'} = (1, (κ_{c←c'})_{c≠c'})` (`prop:depthdir`).
* Windows `W c c' = W_{c←c'} ⊆ 𝔽` (row `c` affected, column `c'` carrying; own window
  `Wo^{(c')} = W c' c'`), the column window `colWin W c' = W^{(c')} = Wo^{(c')} × ∏_{c≠c'} W_{c←c'}`
  (`sec:steer`), and the covering condition `LinesMeet α S` (every line `β + 𝔽 α` meets `S`; condition
  (ii) of `prop:steer`).
* `ownKer`, `crossKer`: the kernels `ŵ_{c'}(z_{c'}(θx))` and `χ_{cc'}(z_{c'}(θx))` of `prop:LI`(c);
  `colVec … ψ l` = the column vector `v_l = (O^{(l)}_{c'}, (X^{(l+1)}_{c←c'})_{c≠c'})` of column `c'`
  computed from a free series `ψ` written in `x` (Lean normalisation: `ψ = ψ_{c'}(θx)`, so the paper's
  digit `ψ_{c',l}` is `coeff l ψ / θ^l`).
* Histories and digits in the PAPER normalisation: a history is a digit sequence `h : ℕ → 𝔽` (the
  coefficients `ψ_{c',n}` of `ψ_{c'}(w)`), of which only `h 0, …, h (l-1)` are read at depth `l`
  (`histSer h l`); `stBeta … h l` = the offset `β_l` of `prop:depthdir` (it depends only on the history);
  `Admissible … h l ψ` ⟺ `β_l - θ^l ψ α_{c'} ∈ W^{(c')}` (`sec:steer`).
* `IsSelRule`: a selection rule assigns to each column, depth `l ≥ 1` and history (`h 0 = 1`) an
  admissible digit; `ruleHist`, `ruleDigit`: the digits it chooses depth by depth (`ψ_{c',0} = 1`);
  `ruleMult`: the multipliers of the resulting self-similar scramble, `g_{c'} = λ_{c'}/(ψ_{c'}(θx) w'(z_{c'}))`
  (`prop:LI`(a), λ-form).
* `RespInS`: all one-digit responses lie in their windows; `sumsetS`, `WinLB`: the sumset `S_c(e)` and the
  window bound `LB(W)` (`sec:steer`), as the statement "`LB ≤ LB(W)`" in pointwise form.
* `fbar`: the one-digit gap `f̄(e, Φ)` on `ℝ/ℤ` (`lem:antipode`), written as a `1`-periodic function on `ℝ`.
-/

namespace GeoSeq

open Finset PowerSeries

section Frame

variable {F : Type*} [Field F] {s : ℕ}

/-- **The depth-zero cross, `λ`-form** (`prop:LI`(c)): `κ_{c←c'} = θ λ_c/(λ_{c'} w'(a_c) (a_{c'} - a_c))`. -/
noncomputable def kapL (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (c c' : Fin s) : F :=
  θ * lamv c / (lamv c' * placeDer zθ c * (ssPlace zθ c' - ssPlace zθ c))

/-- **The depth direction** of column `c'` (`prop:depthdir`): `α_{c'} = (1, (κ_{c←c'})_{c≠c'})`, own entry
(row `c'`) equal to `1`. -/
noncomputable def stAlpha (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (c' : Fin s) :
    Fin s → F :=
  fun c => if c = c' then 1 else kapL θ lamv zθ c c'

/-- **The column window** `W^{(c')} = Wo^{(c')} × ∏_{c≠c'} W_{c←c'}` (`sec:steer`), with `W c c' = W_{c←c'}`
(own window `Wo^{(c')} = W c' c'`): the vectors whose entry `c` lies in `W_{c←c'}` for every row `c`. -/
def colWin (W : Fin s → Fin s → Set F) (c' : Fin s) : Set (Fin s → F) :=
  {v | ∀ c, v c ∈ W c c'}

/-- **Covering condition** (condition (ii) of `prop:steer`): every line `β + 𝔽 α`, `β ∈ 𝔽^s`, meets `S`. -/
def LinesMeet (α : Fin s → F) (S : Set (Fin s → F)) : Prop :=
  ∀ β : Fin s → F, ∃ t : F, β + t • α ∈ S

/-- The own kernel `ŵ_{c'}(z_{c'}(θx)) = ∏_{c≠c'} (z_{c'}(θx) - a_c)/w'(a_{c'})` (`prop:LI`(c)). -/
noncomputable def ownKer (zθ : Fin s → PowerSeries F) (c' : Fin s) : PowerSeries F :=
  (∏ c ∈ univ.erase c', (zθ c' - C (ssPlace zθ c))) * C (placeDer zθ c')⁻¹

/-- The cross kernel `χ_{cc'}(z_{c'}(θx)) = (a_{c'} - a_c)/(z_{c'}(θx) - a_c)` (`prop:LI`(c)). -/
noncomputable def crossKer (zθ : Fin s → PowerSeries F) (c c' : Fin s) : PowerSeries F :=
  C (ssPlace zθ c' - ssPlace zθ c) * (zθ c' - C (ssPlace zθ c))⁻¹

/-- **The column vector** `v_l = (O^{(l)}_{c'}, (X^{(l+1)}_{c←c'})_{c≠c'}) ∈ 𝔽^s` of column `c'` at depth `l`
(`sec:steer`), computed by `prop:LI`(c) from the free series `ψ` of column `c'` written in `x`
(`ψ = ψ_{c'}(θx)`): `O^{(l)} = [x^l] (1 - ŵ_{c'} ψ)/(1 - x)` and
`X^{(l+1)}_{c←c'} = [x^{l+1}] x (-κ_{c←c'} χ_{cc'} ψ)/(1 - x)` (partial sums of `O_{c'}` and `X_{c←c'}`). -/
noncomputable def colVec (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (c' : Fin s)
    (ψ : PowerSeries F) (l : ℕ) : Fin s → F :=
  fun c => if c = c' then coeff l ((1 - ownKer zθ c' * ψ) * PowerSeries.mk 1)
    else coeff (l + 1) (X * (-C (kapL θ lamv zθ c c') * crossKer zθ c c' * ψ) * PowerSeries.mk 1)

/-- The series of a history truncated at depth `l` (paper normalisation, in `w`):
`∑_{n<l} h_n w^n` (the digits `ψ_{c',0}, …, ψ_{c',l-1}`). -/
def histSer (h : ℕ → F) (l : ℕ) : PowerSeries F :=
  PowerSeries.mk fun n => if n < l then h n else 0

/-- **The offset** `β_l` of `prop:depthdir` for the history `h` (paper digits `ψ_{c',0}, …, ψ_{c',l-1}`):
the column vector at depth `l` of the free series `ψ_{c'}(θx)` with digit `l` set to `0` (only
`h 0, …, h (l-1)` are read). -/
noncomputable def stBeta (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (c' : Fin s)
    (h : ℕ → F) (l : ℕ) : Fin s → F :=
  colVec θ lamv zθ c' (rescale θ (histSer h l)) l

/-- **Admissible digit** (`sec:steer`): the digit `ψ ∈ 𝔽` is admissible at depth `l` for column `c'` and
history `h` if `β_l - θ^l ψ α_{c'} ∈ W^{(c')}`. -/
def Admissible (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (W : Fin s → Fin s → Set F)
    (c' : Fin s) (h : ℕ → F) (l : ℕ) (ψ : F) : Prop :=
  stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c' ∈ colWin W c'

/-- **Selection rule** (`sec:steer`): `rule c' l h` is an admissible digit for column `c'` at every depth
`l ≥ 1` and every history `h` (`h 0 = ψ_{c',0} = 1`; the rule is only ever applied to `h` truncated at
depth `l`, see `ruleHist`). -/
def IsSelRule (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (W : Fin s → Fin s → Set F)
    (rule : Fin s → ℕ → (ℕ → F) → F) : Prop :=
  ∀ c' l (h : ℕ → F), 1 ≤ l → h 0 = 1 → Admissible θ lamv zθ W c' h l (rule c' l h)

/-- The history after `l` choices of a rule `r` for one column: digits `0, …, l-1` (`ψ_0 = 1`, then
`ψ_n = r n (history after n choices)`), zero from `l` on. -/
def ruleHist (r : ℕ → (ℕ → F) → F) : ℕ → ℕ → F
  | 0 => fun _ => 0
  | l + 1 => fun n => if n < l then ruleHist r l n
      else if n = l then (if l = 0 then 1 else r l (ruleHist r l)) else 0

/-- The digits `ψ_{c',n}` chosen by a selection rule (paper normalisation): `ψ_{c',0} = 1`,
`ψ_{c',l} = rule c' l (history)` for `l ≥ 1`. -/
def ruleDigit (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) (n : ℕ) : F :=
  ruleHist (rule c') (n + 1) n

/-- **The scramble of a selection rule** (`prop:LI`(a), λ-form `λ_{c'} φ_{c'} = g_{c'} w'(z_{c'})`,
`ψ_{c'} = 1/φ_{c'}`): `g_{c'}(x) = λ_{c'}/(ψ_{c'}(θx) ∏_{c≠c'} (z_{c'}(θx) - z_c(θx)))` with
`ψ_{c'}(w) = ∑_n ψ_{c',n} w^n` the chosen digits. -/
noncomputable def ruleMult (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (rule : Fin s → ℕ → (ℕ → F) → F) : Fin s → PowerSeries F :=
  fun c' => C (lamv c') *
    (rescale θ (PowerSeries.mk (ruleDigit rule c')) * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹

/-- The strip windows of `fig:cost`(b): own window `{o}` and full cross windows (`W_{c←c'} = 𝔽`); used for
the non-vacuity instance of `prop:steer`. -/
def stripWin (o : F) : Fin s → Fin s → Set F := fun c c' => if c = c' then {o} else Set.univ

end Frame

section Windows

variable {s : ℕ}

/-- **All responses lie in their windows** (`prop:steer`(c)): every one-digit response
`D(l)[c][c']` (`j = 1`, every level `K`, carry length `1 ≤ l ≤ K`) lies in `W_{c←c'}`, i.e.
`O^{(l)}_{c} ∈ Wo^{(c)}` and `X^{(l)}_{c←c'} ∈ W_{c←c'}`. -/
def RespInS {p : ℕ} (C : Gen s (ZMod p)) (W : Fin s → Fin s → Set (ZMod p)) : Prop :=
  ∀ K l : ℕ, 1 ≤ l → l ≤ K → ∀ c c' : Fin s, ∀ d : ZMod p,
    IsCarryEntry C K 0 l c c' d → d ∈ W c c'

/-- **The sumset** `S_c(e) = ∑_{c' : e_{c'} ≠ 0} e_{c'} W_{c←c'}` (`sec:steer`). -/
def sumsetS {p : ℕ} (W : Fin s → Fin s → Set (ZMod p)) (e : Fin s → ℤ) (c : Fin s) : Set (ZMod p) :=
  {σ | ∃ x : Fin s → ZMod p, (∀ c', e c' ≠ 0 → x c' ∈ W c c') ∧
    σ = ∑ c', (e c' : ZMod p) * x c'}

/-- **`LB ≤ LB(W)`**, the window bound of `sec:steer`,
`LB(W)² = min_e ∑_c min_{σ ∈ S_c(e)} f_1(e_c, σ)²` over the steps `e ∈ {-1,0,1}^s \ {0}`, in pointwise form:
for every step `e` and every choice `σ_c ∈ S_c(e)` (independently for each `c`),
`LB ≤ (∑_c f_1(e_c, σ_c)²)^{1/2}`, `f_1 = gapNum1 / p` (`rem:onedigit`). The paper takes the minimum over
the steps up to sign; the term is invariant under `(e, σ) ↦ (-e, -σ)` (`gapNum1_neg`, `sumsetS_neg`), so
quantifying over all steps is the same. -/
def WinLB (p : ℕ) [NeZero p] (W : Fin s → Fin s → Set (ZMod p)) (LB : ℝ) : Prop :=
  ∀ e : Fin s → ℤ, (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
    ∀ σ : Fin s → ZMod p, (∀ c, σ c ∈ sumsetS W e c) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2)

end Windows

/-- **The one-digit gap** `f̄(e, Φ)` of `lem:antipode` on `ℝ/ℤ` (as a `1`-periodic function of `Φ ∈ ℝ`):
`f̄(+1, Φ) = 1 - frac(-Φ)`, `f̄(-1, Φ) = f̄(+1, -Φ) = 1 - frac(Φ)` (`fbar_neg_one`),
`f̄(0, Φ) = ‖Φ‖ = min(frac Φ, 1 - frac Φ)` (the distance of `Φ` to the nearest integer); `0` for other `e`. -/
noncomputable def fbar (e : ℤ) (Φ : ℝ) : ℝ :=
  if e = 1 then 1 - Int.fract (-Φ) else if e = -1 then 1 - Int.fract Φ
  else if e = 0 then min (Int.fract Φ) (1 - Int.fract Φ) else 0

end GeoSeq
