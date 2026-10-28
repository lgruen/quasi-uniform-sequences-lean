/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V1Defs
public import GeoSeq.L3Defs

@[expose] public section

/-!
# Statements: stage V1 (general window machinery, `prop:steer`, `prop:depthdir` offset form, `lem:antipode`)

PROVED (`GeoSeq/V1.lean`, `GeoSeq/V1Aux.lean`); generated verbatim from the proof files' signatures
(definitions in `GeoSeq/V1Defs.lean`). Paper: V3 (development version V3 of the paper, `04-steer.tex`); label → Lean
map in the formalization notes of the research repository.

* **`steer`** = `prop:steer` (a)–(d), every `s`, every frame of distinct places, fixed `θ ≠ 0`, constants
  `λ_c ≠ 0`, product windows `W_{c←c'}`; "every selection rule" is the universal quantification over
  `IsSelRule`, and `steer_every` shows that this is the same as every multiplier family with the constants
  `λ_c` whose responses all lie in the windows (so the bound depends only on the windows).
  Parts: `steer_a` (a), `selRule_exists`, `ruleMult_facts` (b, the scramble), `win_cert_S` (d from (c)).
* **`depthdir_V1`** = `prop:depthdir` in the offset form `v_l = β_l + ψ̄_l α_{c'}`, `ψ̄_l = -θ^l ψ_{c',l}`
  (every `s`, every frame), from `resp_colVec` (`prop:law` + `prop:LI`(c) + `LI_c_lambda`), `colVec_dir`,
  `colVec_rescale`, `stBeta_congr`; frame facts `coeff1_place`, `ownKer_const`, `crossKer_const`,
  `colVec_zero_cross` (`X^{(1)} = -κ`).
* `steer_volume` = `lem:volume` for the column windows under (ii) of `prop:steer`.
* `gapNum1_neg`, `sumsetS_neg`: `LB(W)` "up to sign" = over all steps.
* **`antipode_f1`**, **`antipode_agree`**, `antipode_half`, `fbar_neg_one` = `lem:antipode`.
* `steer_nonvacuous`: the hypotheses of `steer` hold (s = 3, p = 7, Kummer frame, strip windows).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Frame

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

/-- `[x] z_c(θx) · w'(a_c) = θ` (differentiate `w(z_c(θx)) = θx` at `x = 0`). -/
theorem coeff1_place (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (c : Fin s) : coeff 1 (zθ c) * placeDer zθ c = θ := by
  sorry

/-- The own kernel takes the value `1` at `x = 0`. -/
theorem ownKer_const (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) :
    constantCoeff (ownKer zθ c') = 1 := by
  sorry

/-- The cross kernel takes the value `1` at `x = 0` (`c ≠ c'`). -/
theorem crossKer_const (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c c' : Fin s)
    (hc : c ≠ c') : constantCoeff (crossKer zθ c c') = 1 := by
  sorry

/-- **Depth direction** (`prop:depthdir`): if two free series agree below `x^l`, their column vectors at
depth `l` differ by `-(ψ_l - ψ'_l) α_{c'}`. -/
theorem colVec_dir (θ : F) (lamv : Fin s → F) (zθ : Fin s → PS)
    (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) (ψ ψ' : PS) (l : ℕ)
    (h : ∀ n < l, coeff n ψ = coeff n ψ') :
    colVec θ lamv zθ c' ψ l =
      colVec θ lamv zθ c' ψ' l - (coeff l ψ - coeff l ψ') • stAlpha θ lamv zθ c' := by
  sorry

/-- **Offset form of the depth direction** (`prop:depthdir`): for every series `ψ` (paper normalisation,
in `w`), the column vector of the free series `ψ(θx)` at depth `l` is `β_l - θ^l ψ_l α_{c'}`, where `β_l` is
the offset of the history `ψ_0, …, ψ_{l-1}`. -/
theorem colVec_rescale (θ : F) (lamv : Fin s → F) (zθ : Fin s → PS)
    (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) (ψ : PS) (l : ℕ) :
    colVec θ lamv zθ c' (rescale θ ψ) l =
      stBeta θ lamv zθ c' (fun n => coeff n ψ) l - (θ ^ l * coeff l ψ) • stAlpha θ lamv zθ c' := by
  sorry

/-- The offset `β_l` depends only on the history `h 0, …, h (l-1)`. -/
theorem stBeta_congr (θ : F) (lamv : Fin s → F) (zθ : Fin s → PS) (c' : Fin s) (h h' : ℕ → F)
    (l : ℕ) (hh : ∀ n < l, h n = h' n) :
    stBeta θ lamv zθ c' h l = stBeta θ lamv zθ c' h' l := by
  sorry

end Frame

section Rules

variable {F : Type*} [Field F] {s : ℕ}

theorem ruleDigit_zero (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) : ruleDigit rule c' 0 = 1 := by
  sorry

theorem ruleDigit_succ (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) (l : ℕ) (hl : 1 ≤ l) :
    ruleDigit rule c' l = rule c' l (ruleHist (rule c') l) := by
  sorry

/-- The history after `l` choices: the chosen digits `0, …, l-1`, zero from `l` on. -/
theorem ruleHist_eq (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) (l : ℕ) :
    ruleHist (rule c') l = fun n => if n < l then ruleDigit rule c' n else 0 := by
  sorry

/-- **`prop:steer`(a)**: under the covering condition (ii), at every depth and for every history admissible
digits exist, and `ψ ↦ O^{(l)}_{c'}` (the own entry of `β_l - θ^l ψ α_{c'}`) is a bijection from the admissible
digits onto the own entries of the points of `W^{(c')}` on the line `β_l + 𝔽 α_{c'}`. -/
theorem steer_a (θ : F) (hθ : θ ≠ 0) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (W : Fin s → Fin s → Set F) (c' : Fin s)
    (hii : LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) (h : ℕ → F) (l : ℕ) :
    (∃ ψ : F, Admissible θ lamv zθ W c' h l ψ) ∧
    Set.BijOn (fun ψ : F => (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c')
      {ψ | Admissible θ lamv zθ W c' h l ψ}
      {o | ∃ v ∈ colWin W c', (∃ t : F, v = stBeta θ lamv zθ c' h l + t • stAlpha θ lamv zθ c') ∧
        v c' = o} := by
  sorry

/-- **A selection rule exists** whenever the covering condition (ii) holds for every column. -/
theorem selRule_exists (θ : F) (hθ : θ ≠ 0) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (W : Fin s → Fin s → Set F) (hii : ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    ∃ rule : Fin s → ℕ → (ℕ → F) → F, IsSelRule θ lamv zθ W rule := by
  sorry

/-- **Every selection rule defines a self-similar scramble** with the constants `λ_c` (`prop:LI`(a)):
`g_c(0) ≠ 0`, `λ_c = g_c(0) w'(a_c)`, and the free series of column `c` is `ψ_c(θx)` with `ψ_c` the chosen
digits. -/
theorem ruleMult_facts (θ : F) (lamv : Fin s → F) (hlam : ∀ c, lamv c ≠ 0)
    (zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ))
    (rule : Fin s → ℕ → (ℕ → F) → F) (c : Fin s) :
    constantCoeff (ruleMult θ lamv zθ rule c) ≠ 0 ∧ lam (ruleMult θ lamv zθ rule) zθ c = lamv c ∧
      freeSer (ruleMult θ lamv zθ rule) zθ c = rescale θ (PowerSeries.mk (ruleDigit rule c)) := by
  sorry

end Rules

section Resp

variable {F : Type*} [Field F] {s : ℕ}

/-- The depth-zero cross: `X^{(1)}_{c←c'} = -κ_{c←c'}` (entry `c ≠ c'` of `v_0`, as `ψ(0) = 1`). -/
theorem colVec_zero_cross (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (c c' : Fin s) (hc : c ≠ c') (ψ : PowerSeries F)
    (hψ : constantCoeff ψ = 1) : colVec θ lamv zθ c' ψ 0 c = -kapL θ lamv zθ c c' := by
  sorry

variable [Fintype F] [DecidableEq F]

/-- **The actual responses are the entries of `colVec`** (`prop:law`, `prop:LI`(b),(c), λ-form): for a
self-similar scramble of the frame with constants `λ_c` (`g_c(0) ≠ 0`, `λ_c = g_c(0) w'(a_c)`), at EVERY level
`K` the own response `O^{(l)}_{c'}` (`l ≤ K`) and the cross responses `X^{(l+1)}_{c←c'}` (`l + 1 ≤ K`) are the
entries of the column vector `v_l` of the free series `freeSer g zθ c'`. -/
theorem resp_colVec (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0)
    (zθ : Fin s → PowerSeries F) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin s → F) (g : Fin s → PowerSeries F)
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (hlam : ∀ c, lam g zθ c = lamv c) (c' : Fin s) :
    (∀ K l, 1 ≤ l → l ≤ K →
      IsCarryEntry (ssGen g zθ) K 0 l c' c' (colVec θ lamv zθ c' (freeSer g zθ c') l c')) ∧
    (∀ c, c ≠ c' → ∀ K l, l + 1 ≤ K →
      IsCarryEntry (ssGen g zθ) K 0 (l + 1) c c' (colVec θ lamv zθ c' (freeSer g zθ c') l c)) := by
  sorry

end Resp

section Main

variable {s : ℕ}

/-- **`prop:steer`(d) from (c)** (`lem:cert` with `j = 1`; any digital `(0,s)`-sequence over `𝔽_p`, `p ≥ 5`):
if all one-digit responses lie in the windows and `LB ≤ LB(W)`, then for every `K ≥ 1` every term of the
certificate `LB^{act}_K` (computed from the actual responses `D(l)`) is `≥ LB`, and `c(P_{sK}) ≥ min(1, LB)`. -/
theorem win_cert_S (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (C : Gen s (ZMod p))
    (hseq : IsSeq0 (zcode p) C) (W : Fin s → Fin s → Set (ZMod p)) (hW : RespInS C W) (LB : ℝ)
    (hLB : WinLB p W LB) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ∀ d : Fin s → Fin s → ZMod p,
      (∀ c c', IsCarryEntry C K 0 (l c') c c' (d c c')) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2)) ∧
    SepAtLevel p s K (seqPoint (zcode p) C) (min 1 LB) := by
  sorry

end Main

section Steer

variable {s : ℕ}

/-- **`prop:depthdir`** (offset form; every `s`, every frame of distinct places, constants `λ_c`): for a
self-similar scramble with `g_c(0) ≠ 0` and `λ_c = g_c(0) w'(a_c)`, write the free series of column `c'` as
`ψ_{c'}(θx)` (`rescale θ ψ = freeSer g zθ c'`, `ψ` in the paper normalisation). Then the depth-zero crosses
are `X^{(1)}_{c←c'} = -κ_{c←c'}`, and at every depth `l ≥ 1` and every level `K ≥ l + 1`
`v_l = (O^{(l)}_{c'}, (X^{(l+1)}_{c←c'})_{c≠c'}) = β_l + ψ̄_l α_{c'}`, `α_{c'} = (1, (κ_{c←c'})_{c≠c'})`,
`ψ̄_l = -θ^l ψ_{c',l}`, where the offset `β_l = stBeta … (ψ_{c',n})_n l` depends only on
`ψ_{c',0}, …, ψ_{c',l-1}` (last clause). The freeness of the digits is `freeSer_free` (stage S10) and
`ruleMult_facts`; the row dependence is `freeSer_row` (stage S10). -/
theorem depthdir_V1 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (w : F[X]) (hw : w.Monic)
    (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (lamv : Fin s → F) (g : Fin s → PowerSeries F) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hlam : ∀ c, lam g zθ c = lamv c) (c' : Fin s) (ψ : PowerSeries F)
    (hψ : rescale θ ψ = freeSer g zθ c') :
    (∀ c, c ≠ c' → ∀ K, 1 ≤ K → IsCarryEntry (ssGen g zθ) K 0 1 c c' (-kapL θ lamv zθ c c')) ∧
    (∀ l, 1 ≤ l → ∀ K, l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c' c'
      ((stBeta θ lamv zθ c' (fun n => coeff n ψ) l +
        (-(θ ^ l * coeff l ψ)) • stAlpha θ lamv zθ c') c')) ∧
    (∀ l, 1 ≤ l → ∀ K, l + 1 ≤ K → ∀ c, c ≠ c' → IsCarryEntry (ssGen g zθ) K 0 (l + 1) c c'
      ((stBeta θ lamv zθ c' (fun n => coeff n ψ) l +
        (-(θ ^ l * coeff l ψ)) • stAlpha θ lamv zθ c') c)) ∧
    (∀ (h h' : ℕ → F) (l : ℕ), (∀ n < l, h n = h' n) →
      stBeta θ lamv zθ c' h l = stBeta θ lamv zθ c' h' l) := by
  sorry

/-- **`prop:steer`** (choosing within windows; every `s`, every frame of distinct places, fixed `θ ≠ 0` and
constants `λ_c ≠ 0`). Let `p ≥ 5` be prime, let the local roots `z_c(θx)` of the frame `w` (monic of degree
`s`, `w(z_c(θx)) = θx`) have distinct places, and let the windows `W_{c←c'}` satisfy, for every column `c'`,
(i) `-κ_{c←c'} ∈ W_{c←c'}` for all `c ≠ c'`, and (ii) every line `β + 𝔽_p α_{c'}` meets `W^{(c')}`. Then
(a) at every depth `l ≥ 1` and for every history admissible digits exist, and `ψ ↦ O^{(l)}_{c'}` is a
bijection from the admissible digits onto the own entries of the points of `W^{(c')}` on the line
`β_l + 𝔽_p α_{c'}`; a selection rule exists; and for EVERY selection rule: (b) it defines a self-similar
scramble (multipliers `g_c = λ_c/(ψ_c(θx) w'(z_c))` with `g_c(0) ≠ 0`, constants `λ_c`, free series the chosen
digits) and the sequence is a digital `(0,s)`-sequence over `𝔽_p`; (c) all responses lie in their windows;
(d) for every `K ≥ 1` and every `LB ≤ LB(W)`, every term of `LB^{act}_K` (`lem:cert`, `j = 1`, actual
responses) is `≥ LB`, and `c(P_{sK}) ≥ min(1, LB)`.

For `s = 2` the paper normalises `ψ` by `ϖ̂_c = z - a_{1-c}` (`prop:LI`(d)); here `ϖ̂ = 1` for every `s`, which
for `s = 2` (Faure places) changes the digit at depth `l` by a translation depending only on the history, so
(a)–(d) are the same statements. -/
theorem steer (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (w : (ZMod p)[X]) (hw : w.Monic)
    (hdeg : w.natDegree = s) (θ : ZMod p) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (lamv : Fin s → ZMod p) (hlam : ∀ c, lamv c ≠ 0) (W : Fin s → Fin s → Set (ZMod p))
    (hi : ∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ W c c')
    (hii : ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    (∀ c' (h : ℕ → ZMod p) (l : ℕ), 1 ≤ l →
      (∃ ψ : ZMod p, Admissible θ lamv zθ W c' h l ψ) ∧
      Set.BijOn (fun ψ : ZMod p => (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c')
        {ψ | Admissible θ lamv zθ W c' h l ψ}
        {o | ∃ v ∈ colWin W c', (∃ t : ZMod p, v = stBeta θ lamv zθ c' h l + t • stAlpha θ lamv zθ c') ∧
          v c' = o}) ∧
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ W rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ W rule →
      (∀ c, constantCoeff (ruleMult θ lamv zθ rule c) ≠ 0 ∧ lam (ruleMult θ lamv zθ rule) zθ c = lamv c ∧
        freeSer (ruleMult θ lamv zθ rule) zθ c = rescale θ (PowerSeries.mk (ruleDigit rule c))) ∧
      IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ) ∧
      RespInS (ssGen (ruleMult θ lamv zθ rule) zθ) W ∧
      ∀ LB : ℝ, WinLB p W LB → ∀ K : ℕ, 1 ≤ K →
        (∀ e l, IsStep K e l → ∀ d : Fin s → Fin s → ZMod p,
          (∀ c c', IsCarryEntry (ssGen (ruleMult θ lamv zθ rule) zθ) K 0 (l c') c c' (d c c')) →
          LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2)) ∧
        SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ)) (min 1 LB) := by
  sorry

/-- **"Every selection rule" = every multiplier family with all responses in the windows**
(`prop:steer`, the remark after it): under (ii), every self-similar scramble of the frame with the constants
`λ_c` (`g_c(0) ≠ 0`, `λ_c = g_c(0) w'(a_c)`) whose one-digit responses all lie in the windows is the scramble
`ruleMult` of some selection rule. Together with `steer` (which applies to every rule), the bound of
`prop:steer`(d) holds for every such scramble and depends only on the windows. -/
theorem steer_every (p : ℕ) [Fact p.Prime] (w : (ZMod p)[X]) (hw : w.Monic)
    (hdeg : w.natDegree = s) (θ : ZMod p) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (lamv : Fin s → ZMod p) (W : Fin s → Fin s → Set (ZMod p))
    (hii : ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin W c'))
    (g : Fin s → PowerSeries (ZMod p)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hlam : ∀ c, lam g zθ c = lamv c) (hW : RespInS (ssGen g zθ) W) :
    ∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule θ lamv zθ W rule ∧ ruleMult θ lamv zθ rule = g := by
  sorry

end Steer

section Sign

/-- `f_1(-e, -σ) = f_1(e, σ)` (the certificate term is invariant under reversing the step). -/
theorem gapNum1_neg (p : ℕ) [NeZero p] (e : ℤ) (σ : ZMod p) :
    gapNum1 p (-e) (-σ) = gapNum1 p e σ := by
  sorry

/-- `S_c(-e) = -S_c(e)`. -/
theorem sumsetS_neg {s p : ℕ} (W : Fin s → Fin s → Set (ZMod p)) (e : Fin s → ℤ) (c : Fin s)
    (σ : ZMod p) : -σ ∈ sumsetS W (-e) c ↔ σ ∈ sumsetS W e c := by
  sorry

end Sign

section Volume

/-- **`lem:volume`** for the column windows of `prop:steer` (the "in particular" clause): if condition (ii)
holds for column `c'`, then `|Wo^{(c')}| ∏_{c≠c'} |W_{c←c'}| ≥ p^{s-1}`. -/
theorem steer_volume {s : ℕ} (p : ℕ) [Fact p.Prime] (θ : ZMod p) (lamv : Fin s → ZMod p)
    (zθ : Fin s → PowerSeries (ZMod p)) (W : Fin s → Fin s → Set (ZMod p)) (c' : Fin s)
    (hii : LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    p ^ (s - 1) ≤ (W c' c').ncard * ∏ c ∈ univ.erase c', (W c c').ncard := by
  sorry

end Volume

section Antipode

/-- `f̄(-1, Φ) = f̄(+1, -Φ)` (`lem:antipode`). -/
theorem fbar_neg_one (Φ : ℝ) : fbar (-1) Φ = fbar 1 (-Φ) := by
  sorry

/-- **`lem:antipode`** (one geometric digit): for `σ ∈ ℤ/pℤ` and `Φ = σ/p ∈ ℝ/ℤ` (representative
`val σ / p`), `f_1(e, σ) = max(0, f̄(e, Φ) - 1/p)` for `e ∈ {-1, 0, 1}`. -/
theorem antipode_f1 (p : ℕ) [NeZero p] (e : ℤ) (he : e = -1 ∨ e = 0 ∨ e = 1) (σ : ZMod p) :
    (gapNum1 p e σ : ℝ) / p = max 0 (fbar e ((σ.val : ℝ) / p) - 1 / p) := by
  sorry

/-- **`lem:antipode`, the antipode**: the three functions `f̄(+1, ·)`, `f̄(-1, ·)`, `f̄(0, ·)` agree at `Φ`
exactly when `Φ ≡ 1/2 (mod 1)`. -/
theorem antipode_agree (Φ : ℝ) :
    (fbar 1 Φ = fbar (-1) Φ ∧ fbar (-1) Φ = fbar 0 Φ) ↔ Int.fract Φ = 1 / 2 := by
  sorry

/-- **`lem:antipode`**: at `Φ ≡ 1/2` all three functions equal `1/2`. -/
theorem antipode_half (Φ : ℝ) (h : Int.fract Φ = 1 / 2) :
    fbar 1 Φ = 1 / 2 ∧ fbar (-1) Φ = 1 / 2 ∧ fbar 0 Φ = 1 / 2 := by
  sorry

end Antipode

section NonVacuous

/-- **Non-vacuity of `steer`** (`prop:steer`): its hypotheses hold for `s = 3`, `p = 7`, the Kummer frame
`w = z³ - 1` with local roots `z_c(θx) = 2^c (1 + θx)^{1/3}` (places `1, 2, 4`), `θ = 1`, constants `λ_c = 1`,
and the non-trivial strip windows `Wo^{(c')} = {0}`, `W_{c←c'} = 𝔽_7` (`fig:cost`(b)); a selection rule exists,
and its scramble is a `(0,3)`-sequence over `𝔽_7` with all responses in the windows. -/
theorem steer_nonvacuous :
    (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]).Monic ∧
    (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]).natDegree = 3 ∧
    (∀ c, Polynomial.aeval (kumZ 7 2 1 c) (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]) =
      C 1 * X) ∧
    Function.Injective (ssPlace (kumZ 7 2 1)) ∧
    (∀ c c' : Fin 3, c ≠ c' → -kapL 1 (fun _ => 1) (kumZ 7 2 1) c c' ∈ stripWin 0 c c') ∧
    (∀ c', LinesMeet (stAlpha 1 (fun _ => (1 : ZMod 7)) (kumZ 7 2 1) c') (colWin (stripWin 0) c')) ∧
    ∃ rule : Fin 3 → ℕ → (ℕ → ZMod 7) → ZMod 7,
      IsSelRule 1 (fun _ => 1) (kumZ 7 2 1) (stripWin 0) rule ∧
      IsSeq0 (zcode 7) (ssGen (ruleMult 1 (fun _ => 1) (kumZ 7 2 1) rule) (kumZ 7 2 1)) ∧
      RespInS (ssGen (ruleMult 1 (fun _ => 1) (kumZ 7 2 1) rule) (kumZ 7 2 1)) (stripWin 0) := by
  sorry

end NonVacuous

end GeoSeq
