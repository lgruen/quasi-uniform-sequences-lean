/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V1Defs
public import GeoSeq.V0
public import GeoSeq.Law
public import GeoSeq.Cert
public import GeoSeq.SSFrame
public import GeoSeq.Window

@[expose] public section

/-!
# GeoSeq stage V1: the general window machinery and `prop:steer` (every `s`, every frame)

* Frame facts: `coeff1_place` (`[x] z_c(θx) · w'(a_c) = θ`), `ownKer_const`, `crossKer_const` (both kernels
  of `prop:LI`(c) take the value `1` at `x = 0`).
* `colVec_dir`, `colVec_rescale`, `stBeta_congr`: the depth direction in offset form
  (`v_l = β_l - θ^l ψ_{c',l} α_{c'}`, `β_l` depends only on `ψ_{c',0}, …, ψ_{c',l-1}`).
* `resp_colVec`: the actual carry responses of a self-similar scramble with constants `λ_c` are the
  entries of `colVec` (`prop:law` + `prop:LI`(c) + the λ-form `LI_c_lambda`), at every level.
* **`depthdir_V1`** (`prop:depthdir`, offset form, every `s`, every frame).
* **`steer_a`** (`prop:steer`(a)), `selRule_exists`, `ruleMult_facts`, **`win_cert_S`** (`prop:steer`(d) from
  (c), any digital sequence), **`steer`** (`prop:steer` (a)–(d)), **`steer_every`** (every multiplier family
  with the constants `λ_c` and all responses in the windows is the scramble of a selection rule: "every
  selection rule" = "every such family").
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Frame

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

lemma v1_coeff1_mul (φ ψ : PS) (hφ : constantCoeff φ = 0) :
    coeff 1 (φ * ψ) = coeff 1 φ * constantCoeff ψ := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp [coeff_zero_eq_constantCoeff_apply, hφ]

/-- `[x] z_c(θx) · w'(a_c) = θ` (differentiate `w(z_c(θx)) = θx` at `x = 0`). -/
theorem coeff1_place (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (c : Fin s) : coeff 1 (zθ c) * placeDer zθ c = θ := by
  have hs : 1 ≤ s := Fin.pos c
  have h := hroot c
  rw [aeval_eq_eval_map, frame_factor_F w hw hdeg θ zθ hroot hinj hs, Polynomial.map_prod,
    Polynomial.eval_prod, ← Finset.mul_prod_erase univ _ (Finset.mem_univ c)] at h
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at h
  have h1 := congrArg (coeff 1) h
  rw [v1_coeff1_mul _ _ (by simp [ssPlace]), map_prod] at h1
  simpa [placeDer, ssPlace] using h1

/-- The own kernel takes the value `1` at `x = 0`. -/
theorem ownKer_const (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) :
    constantCoeff (ownKer zθ c') = 1 := by
  unfold ownKer
  rw [map_mul, map_prod, constantCoeff_C]
  have : ∏ c ∈ univ.erase c', constantCoeff (zθ c' - C (ssPlace zθ c)) = placeDer zθ c' := by
    simp [placeDer, ssPlace]
  rw [this]
  exact mul_inv_cancel₀ (placeDer_ne_zero zθ hinj c')

/-- The cross kernel takes the value `1` at `x = 0` (`c ≠ c'`). -/
theorem crossKer_const (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c c' : Fin s)
    (hc : c ≠ c') : constantCoeff (crossKer zθ c c') = 1 := by
  unfold crossKer
  have hne : ssPlace zθ c' - ssPlace zθ c ≠ 0 := sub_ne_zero.2 fun h => hc (hinj h.symm)
  rw [map_mul, constantCoeff_C, constantCoeff_inv, map_sub, constantCoeff_C]
  exact mul_inv_cancel₀ hne

/-- **Depth direction** (`prop:depthdir`): if two free series agree below `x^l`, their column vectors at
depth `l` differ by `-(ψ_l - ψ'_l) α_{c'}`. -/
theorem colVec_dir (θ : F) (lamv : Fin s → F) (zθ : Fin s → PS)
    (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) (ψ ψ' : PS) (l : ℕ)
    (h : ∀ n < l, coeff n ψ = coeff n ψ') :
    colVec θ lamv zθ c' ψ l =
      colVec θ lamv zθ c' ψ' l - (coeff l ψ - coeff l ψ') • stAlpha θ lamv zθ c' := by
  funext c
  by_cases hc : c = c'
  · subst hc
    simp only [colVec, stAlpha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eq_self_iff_true, ite_true,
      mul_one]
    have hd := coeff_dir (ownKer zθ c) ψ ψ' l h
    rw [ownKer_const zθ hinj c, one_mul] at hd
    have e : ∀ φ : PS, (1 - ownKer zθ c * φ) * PowerSeries.mk 1 =
        PowerSeries.mk 1 - ownKer zθ c * φ * PowerSeries.mk 1 := fun φ => by ring
    rw [e, e, map_sub, map_sub]
    linear_combination -hd
  · simp only [colVec, stAlpha, if_neg hc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∀ φ : PS, X * (-C (kapL θ lamv zθ c c') * crossKer zθ c c' * φ) * PowerSeries.mk 1 =
        X * ((-C (kapL θ lamv zθ c c') * crossKer zθ c c') * φ * PowerSeries.mk 1) := fun φ => by ring
    rw [e, e, coeff_succ_X_mul, coeff_succ_X_mul]
    have hd := coeff_dir (-C (kapL θ lamv zθ c c') * crossKer zθ c c') ψ ψ' l h
    have hE : constantCoeff (-C (kapL θ lamv zθ c c') * crossKer zθ c c') = -kapL θ lamv zθ c c' := by
      rw [map_mul, map_neg, constantCoeff_C, crossKer_const zθ hinj c c' hc, mul_one]
    rw [hE] at hd
    linear_combination hd

lemma coeff_rescale_histSer (θ : F) (h : ℕ → F) (l n : ℕ) :
    coeff n (rescale θ (histSer h l)) = if n < l then θ ^ n * h n else 0 := by
  rw [coeff_rescale, histSer, coeff_mk]
  split_ifs <;> simp

/-- **Offset form of the depth direction** (`prop:depthdir`): for every series `ψ` (paper normalisation,
in `w`), the column vector of the free series `ψ(θx)` at depth `l` is `β_l - θ^l ψ_l α_{c'}`, where `β_l` is
the offset of the history `ψ_0, …, ψ_{l-1}`. -/
theorem colVec_rescale (θ : F) (lamv : Fin s → F) (zθ : Fin s → PS)
    (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) (ψ : PS) (l : ℕ) :
    colVec θ lamv zθ c' (rescale θ ψ) l =
      stBeta θ lamv zθ c' (fun n => coeff n ψ) l - (θ ^ l * coeff l ψ) • stAlpha θ lamv zθ c' := by
  unfold stBeta
  rw [colVec_dir θ lamv zθ hinj c' (rescale θ ψ) (rescale θ (histSer (fun n => coeff n ψ) l)) l
    (fun n hn => by rw [coeff_rescale_histSer, if_pos hn, coeff_rescale])]
  rw [coeff_rescale_histSer, if_neg (lt_irrefl l), sub_zero, coeff_rescale]

/-- The offset `β_l` depends only on the history `h 0, …, h (l-1)`. -/
theorem stBeta_congr (θ : F) (lamv : Fin s → F) (zθ : Fin s → PS) (c' : Fin s) (h h' : ℕ → F)
    (l : ℕ) (hh : ∀ n < l, h n = h' n) :
    stBeta θ lamv zθ c' h l = stBeta θ lamv zθ c' h' l := by
  have e : histSer h l = histSer h' l := by
    ext n
    simp only [histSer, coeff_mk]
    split_ifs with hn
    · exact hh n hn
    · rfl
  unfold stBeta
  rw [e]

end Frame

section Rules

variable {F : Type*} [Field F] {s : ℕ}

lemma ruleHist_succ (r : ℕ → (ℕ → F) → F) (l n : ℕ) :
    ruleHist r (l + 1) n = if n < l then ruleHist r l n
      else if n = l then (if l = 0 then 1 else r l (ruleHist r l)) else 0 := rfl

lemma ruleHist_lt (r : ℕ → (ℕ → F) → F) : ∀ l n, n < l → ruleHist r l n = ruleHist r (n + 1) n
  | 0, n, h => absurd h (Nat.not_lt_zero n)
  | l + 1, n, h => by
    rcases Nat.lt_or_ge n l with hn | hn
    · rw [ruleHist_succ, if_pos hn, ruleHist_lt r l n hn]
    · obtain rfl : n = l := by omega
      rfl

lemma ruleHist_ge (r : ℕ → (ℕ → F) → F) : ∀ l n, l ≤ n → ruleHist r l n = 0
  | 0, _, _ => rfl
  | l + 1, n, h => by rw [ruleHist_succ, if_neg (by omega), if_neg (by omega)]

lemma ruleDigit_zero (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) : ruleDigit rule c' 0 = 1 := by
  rw [ruleDigit, ruleHist_succ, if_neg (lt_irrefl 0), if_pos rfl, if_pos rfl]

lemma ruleDigit_succ (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) (l : ℕ) (hl : 1 ≤ l) :
    ruleDigit rule c' l = rule c' l (ruleHist (rule c') l) := by
  rw [ruleDigit, ruleHist_succ, if_neg (lt_irrefl l), if_pos rfl, if_neg (by omega)]

/-- The history after `l` choices: the chosen digits `0, …, l-1`, zero from `l` on. -/
lemma ruleHist_eq (rule : Fin s → ℕ → (ℕ → F) → F) (c' : Fin s) (l : ℕ) :
    ruleHist (rule c') l = fun n => if n < l then ruleDigit rule c' n else 0 := by
  funext n
  split_ifs with h
  · exact ruleHist_lt _ l n h
  · exact ruleHist_ge _ l n (by omega)

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
  set β := stBeta θ lamv zθ c' h l
  set α := stAlpha θ lamv zθ c'
  have hα : α c' = 1 := by simp [α, stAlpha]
  have hθl : θ ^ l ≠ 0 := pow_ne_zero l hθ
  have key : ∀ t : F, θ ^ l * (-t / θ ^ l) = -t := fun t => by field_simp
  refine ⟨?_, Set.BijOn.mk ?_ ?_ ?_⟩
  · obtain ⟨t, ht⟩ := hii β
    refine ⟨-t / θ ^ l, ?_⟩
    show β - (θ ^ l * (-t / θ ^ l)) • α ∈ colWin W c'
    rw [key, neg_smul, sub_neg_eq_add]
    exact ht
  · intro ψ hψ
    exact ⟨_, hψ, ⟨-(θ ^ l * ψ), by rw [neg_smul, sub_eq_add_neg]⟩, rfl⟩
  · intro ψ₁ _ ψ₂ _ he
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hα, mul_one] at he
    have : θ ^ l * ψ₁ = θ ^ l * ψ₂ := by linear_combination -he
    exact mul_left_cancel₀ hθl this
  · rintro o ⟨v, hv, ⟨t, rfl⟩, rfl⟩
    refine ⟨-t / θ ^ l, ?_, ?_⟩
    · show β - (θ ^ l * (-t / θ ^ l)) • α ∈ colWin W c'
      rw [key, neg_smul, sub_neg_eq_add]
      exact hv
    · show (β - (θ ^ l * (-t / θ ^ l)) • α) c' = (β + t • α) c'
      rw [key, neg_smul, sub_neg_eq_add]

/-- **A selection rule exists** whenever the covering condition (ii) holds for every column. -/
theorem selRule_exists (θ : F) (hθ : θ ≠ 0) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (W : Fin s → Fin s → Set F) (hii : ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    ∃ rule : Fin s → ℕ → (ℕ → F) → F, IsSelRule θ lamv zθ W rule :=
  ⟨fun c' l h => Classical.choose (steer_a θ hθ lamv zθ W c' (hii c') h l).1,
    fun c' l h _ _ => Classical.choose_spec (steer_a θ hθ lamv zθ W c' (hii c') h l).1⟩

/-- **Every selection rule defines a self-similar scramble** with the constants `λ_c` (`prop:LI`(a)):
`g_c(0) ≠ 0`, `λ_c = g_c(0) w'(a_c)`, and the free series of column `c` is `ψ_c(θx)` with `ψ_c` the chosen
digits. -/
theorem ruleMult_facts (θ : F) (lamv : Fin s → F) (hlam : ∀ c, lamv c ≠ 0)
    (zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ))
    (rule : Fin s → ℕ → (ℕ → F) → F) (c : Fin s) :
    constantCoeff (ruleMult θ lamv zθ rule c) ≠ 0 ∧ lam (ruleMult θ lamv zθ rule) zθ c = lamv c ∧
      freeSer (ruleMult θ lamv zθ rule) zθ c = rescale θ (PowerSeries.mk (ruleDigit rule c)) := by
  set g := ruleMult θ lamv zθ rule
  have hψ : constantCoeff (rescale θ (PowerSeries.mk (ruleDigit rule c))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_mk, pow_zero, one_mul]
    exact ruleDigit_zero rule c
  have hw := placeDer_ne_zero zθ hinj c
  have hM : g c = C (lamv c / placeDer zθ c * placeDer zθ c) *
      (rescale θ (PowerSeries.mk (ruleDigit rule c)) * ∏ c'' ∈ univ.erase c, (zθ c - zθ c''))⁻¹ := by
    rw [div_mul_cancel₀ _ hw]
    rfl
  have key := freeSer_free g zθ hinj c (lamv c / placeDer zθ c) (div_ne_zero (hlam c) hw) _ hψ
  rw [← hM, Function.update_eq_self] at key
  obtain ⟨h0, h1⟩ := key
  refine ⟨by rw [h0]; exact div_ne_zero (hlam c) hw, ?_, h1⟩
  show constantCoeff (g c) * placeDer zθ c = lamv c
  rw [h0, div_mul_cancel₀ _ hw]

end Rules

section Resp

variable {F : Type*} [Field F] {s : ℕ}

/-- The depth-zero cross: `X^{(1)}_{c←c'} = -κ_{c←c'}` (entry `c ≠ c'` of `v_0`, as `ψ(0) = 1`). -/
theorem colVec_zero_cross (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (c c' : Fin s) (hc : c ≠ c') (ψ : PowerSeries F)
    (hψ : constantCoeff ψ = 1) : colVec θ lamv zθ c' ψ 0 c = -kapL θ lamv zθ c c' := by
  simp only [colVec, if_neg hc]
  rw [show (X : PowerSeries F) * (-C (kapL θ lamv zθ c c') * crossKer zθ c c' * ψ) * PowerSeries.mk 1 =
      X * (-C (kapL θ lamv zθ c c') * crossKer zθ c c' * ψ * PowerSeries.mk 1) by ring,
    coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  simp [crossKer_const zθ hinj c c' hc, hψ]

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
  obtain ⟨G, hMG, -⟩ := frame_inv g zθ hinj hg
  obtain ⟨hO, hX⟩ := LI_c w hw hdeg θ hθ g zθ hroot hinj hg G hMG c'
  refine ⟨fun K l hl hlK => ?_, fun c hc K l hlK => ?_⟩
  · have := law g zθ w hdeg.le θ θ⁻¹ (mul_inv_cancel₀ hθ) hroot G hMG K 0 l hl hlK c' c'
    rw [hO l] at this
    simpa only [colVec, ownKer, eq_self_iff_true, ite_true] using this
  · have := law g zθ w hdeg.le θ θ⁻¹ (mul_inv_cancel₀ hθ) hroot G hMG K 0 (l + 1) (by omega) hlK c c'
    rw [hX c hc (l + 1)] at this
    have hk : kap θ g zθ c c' = kapL θ lamv zθ c c' := by
      rw [LI_c_lambda θ g zθ hinj hg c c' hc, hlam, hlam]
      rfl
    rw [hk] at this
    simpa only [colVec, if_neg hc, crossKer] using this

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
  have part1 : ∀ e l, IsStep K e l → ∀ d : Fin s → Fin s → ZMod p,
      (∀ c c', IsCarryEntry C K 0 (l c') c c' (d c c')) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2) := by
    rintro e l ⟨he, hne, hl⟩ d hd
    exact hLB e he hne (fun c => ∑ c', (e c' : ZMod p) * d c c')
      fun c => ⟨fun c' => d c c', fun c' _ => hW K (l c') (hl c').1 (hl c').2 c c' _ (hd c c'), rfl⟩
  refine ⟨part1, ?_⟩
  have hnet : BlockNet0 (zcode p) C (s * K) 0 := hseq (s * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  classical
  let Dr : ℕ → Fin s → Fin s → ZMod p := fun l c c' =>
    if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists (zcode p) C K hnet 0 l c c') else 0
  have hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c') := by
    intro l h1 h2 c c'
    simp only [Dr, And.intro h1 h2, and_self, dite_true]
    exact Classical.choose_spec (carry_exists (zcode p) C K hnet 0 l c c')
  refine cert_one C K hq hnet Dr hD LB fun e l hst => ?_
  exact part1 e l hst (fun c c' => Dr (l c') c c')
    fun c c' => hD _ (hst.2.2 c').1 (hst.2.2 c').2 c c'

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
  obtain ⟨hO, hX⟩ := resp_colVec w hw hdeg θ hθ zθ hroot hinj lamv g hg hlam c'
  have hv : ∀ l, colVec θ lamv zθ c' (freeSer g zθ c') l =
      stBeta θ lamv zθ c' (fun n => coeff n ψ) l + (-(θ ^ l * coeff l ψ)) • stAlpha θ lamv zθ c' := by
    intro l
    rw [← hψ, colVec_rescale θ lamv zθ hinj c' ψ l, neg_smul, sub_eq_add_neg]
  refine ⟨fun c hc K hK => ?_, fun l hl K hK => ?_, fun l _ K hK c hc => ?_,
    fun h h' l hh => stBeta_congr θ lamv zθ c' h h' l hh⟩
  · have := hX c hc K 0 (by omega)
    rwa [colVec_zero_cross θ lamv zθ hinj c c' hc _ (freeSer_const g zθ hinj hg c')] at this
  · rw [← hv]; exact hO K l hl hK
  · rw [← hv]; exact hX c hc K l hK

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
  refine ⟨fun c' h l _ => steer_a θ hθ lamv zθ W c' (hii c') h l,
    selRule_exists θ hθ lamv zθ W hii, fun rule hrule => ?_⟩
  have hfacts := ruleMult_facts θ lamv hlam zθ hinj rule
  set g := ruleMult θ lamv zθ rule
  have hg : ∀ c, constantCoeff (g c) ≠ 0 := fun c => (hfacts c).1
  have hlg : ∀ c, lam g zθ c = lamv c := fun c => (hfacts c).2.1
  -- the column vectors chosen by the rule lie in the column windows
  have hv : ∀ c' l, 1 ≤ l → colVec θ lamv zθ c' (freeSer g zθ c') l ∈ colWin W c' := by
    intro c' l hl
    have hadm := hrule c' l (ruleHist (rule c') l) hl
      (by rw [ruleHist_lt _ l 0 hl]; exact ruleDigit_zero rule c')
    rw [(hfacts c').2.2, colVec_rescale θ lamv zθ hinj c']
    simp only [coeff_mk]
    have e1 : stBeta θ lamv zθ c' (fun n => ruleDigit rule c' n) l =
        stBeta θ lamv zθ c' (ruleHist (rule c') l) l :=
      stBeta_congr θ lamv zθ c' _ _ l fun n hn => (ruleHist_lt _ l n hn).symm
    rw [e1, ruleDigit_succ rule c' l hl]
    exact hadm
  have hresp : RespInS (ssGen g zθ) W := by
    intro K l hl hlK c c' d hd
    obtain ⟨hO, hX⟩ := resp_colVec w hw hdeg θ hθ zθ hroot hinj lamv g hg hlg c'
    by_cases hc : c = c'
    · subst hc
      rw [carryEntry_unique _ _ _ _ _ _ hd (hO K l hl hlK)]
      exact hv c l hl c
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      rw [carryEntry_unique _ _ _ _ _ _ hd (hX c hc K m hlK)]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [colVec_zero_cross θ lamv zθ hinj c c' hc _ (freeSer_const g zθ hinj hg c')]
        exact hi c c' hc
      · exact hv c' m hm c
  have hseq : IsSeq0 (zcode p) (ssGen g zθ) := by
    refine ss_t0 (zcode p) g zθ hinj hg fun c => ?_
    refine left_ne_zero_of_mul (b := placeDer zθ c) ?_
    rw [coeff1_place w hw hdeg θ zθ hroot hinj c]
    exact hθ
  exact ⟨hfacts, hseq, hresp, fun LB hLB K hK => win_cert_S p hp _ hseq W hresp LB hLB K hK⟩

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
  classical
  set dg : Fin s → ℕ → ZMod p := fun c n => coeff n (rescale θ⁻¹ (freeSer g zθ c)) with hdg
  have hres : ∀ c, rescale θ (PowerSeries.mk (dg c)) = freeSer g zθ c := by
    intro c
    have : PowerSeries.mk (dg c) = rescale θ⁻¹ (freeSer g zθ c) := by ext n; simp [hdg]
    rw [this, rescale_rescale, inv_mul_cancel₀ hθ, rescale_one, RingHom.id_apply]
  have hd0 : ∀ c, dg c 0 = 1 := by
    intro c
    simp only [hdg, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]
    exact freeSer_const g zθ hinj hg c
  have hadm : ∀ c l, 1 ≤ l → Admissible θ lamv zθ W c (dg c) l (dg c l) := by
    intro c l hl
    have hcv := colVec_rescale θ lamv zθ hinj c (PowerSeries.mk (dg c)) l
    rw [hres c] at hcv
    simp only [coeff_mk] at hcv
    show stBeta θ lamv zθ c (dg c) l - (θ ^ l * dg c l) • stAlpha θ lamv zθ c ∈ colWin W c
    rw [← hcv]
    intro c₁
    obtain ⟨hO, hX⟩ := resp_colVec w hw hdeg θ hθ zθ hroot hinj lamv g hg hlam c
    by_cases h1 : c₁ = c
    · subst h1
      exact hW l l hl le_rfl c₁ c₁ _ (hO l l hl le_rfl)
    · exact hW (l + 1) (l + 1) (by omega) le_rfl c₁ c _ (hX c₁ h1 (l + 1) l le_rfl)
  let rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p := fun c l h =>
    if ∀ n < l, h n = dg c n then dg c l
    else Classical.choose (steer_a θ hθ lamv zθ W c (hii c) h l).1
  have hrule : IsSelRule θ lamv zθ W rule := by
    intro c l h hl _
    by_cases hh : ∀ n < l, h n = dg c n
    · simp only [rule, if_pos hh]
      unfold Admissible
      rw [stBeta_congr θ lamv zθ c h (dg c) l hh]
      exact hadm c l hl
    · simp only [rule, if_neg hh]
      exact Classical.choose_spec (steer_a θ hθ lamv zθ W c (hii c) h l).1
  have hhist : ∀ c l, ruleHist (rule c) l = fun n => if n < l then dg c n else 0 := by
    intro c l
    induction l with
    | zero => funext n; simp [ruleHist]
    | succ l ih =>
      funext n
      rw [ruleHist_succ, ih]
      by_cases hn : n < l
      · simp [hn, show n < l + 1 by omega]
      · by_cases hnl : n = l
        · subst hnl
          rw [if_neg hn, if_pos rfl, if_pos (Nat.lt_succ_self n)]
          split_ifs with h0
          · subst h0; exact (hd0 c).symm
          · simp only [rule]
            rw [if_pos fun m hm => by simp [hm]]
        · rw [if_neg hn, if_neg hnl, if_neg (by omega)]
  have hdig : ∀ c, ruleDigit rule c = dg c := by
    intro c; funext n
    simp only [ruleDigit, hhist, Nat.lt_succ_self, if_true]
  refine ⟨rule, hrule, ?_⟩
  funext c
  simp only [ruleMult, hdig, hres]
  rw [← hlam c]
  exact (g_of_freeSer g zθ hinj hg c).symm

end Steer

end GeoSeq
