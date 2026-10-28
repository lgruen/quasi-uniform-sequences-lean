/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7Defs
public import GeoSeq.V1

@[expose] public section

/-!
# GeoSeq stage V7: the graph rule (`def:graphrule`, `app:p7`)

For `s = 3`, any frame of three distinct places, any scale `θ ≠ 0` and any constants `λ_c ≠ 0`:

* **`graphRule_unique`** (realizability, the paragraph before `def:graphrule`): at every depth `l ≥ 1` and for every
  history, the graph rule's digit is the UNIQUE digit `ψ` with own response `O^{(l)}_{c'} = w(X^{(l)}_{c'+1←c'},
  X^{(l)}_{c'+2←c'})` (the crosses at length `l` are known from the history).
* **`graph_resp`**: for the graph-rule scramble, every column of every `D(l)` lies on the graph
  `{(w(ξ); ξ)}` (at every level `K`, `1 ≤ l ≤ K`).
* **`graph_cert`**: every term of `LB^{act}_K` is a term of `LB(w)`, so `LB ≤ LB(w)` gives `c(P_{3K}) ≥ min(1, LB)`.
* **`graph_seq`**: the whole statement: the rule defines a self-similar scramble (constants `λ_c`) and a digital
  `(0,3)`-sequence over `𝔽_p`, the responses lie on the graph, and the bound of `LB(w)` holds at every level.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

lemma fin3_cases (c c' : Fin 3) : c = c' ∨ c = c' + 1 ∨ c = c' + 2 := by
  revert c c'; decide

lemma fin3_ne1 (c' : Fin 3) : c' + 1 ≠ c' := by revert c'; decide

lemma fin3_ne2 (c' : Fin 3) : c' + 2 ≠ c' := by revert c'; decide

lemma fin3_ne21 (c' : Fin 3) : c' + 2 ≠ c' + 1 := by revert c'; decide

section Rule

variable {F : Type*} [Field F]

lemma stAlpha_self (θ : F) (lamv : Fin 3 → F) (zθ : Fin 3 → PowerSeries F) (c' : Fin 3) :
    stAlpha θ lamv zθ c' c' = 1 := by
  simp [stAlpha]

/-- **Realizability of the graph rule** (the paragraph before `def:graphrule`, from `prop:depthdir`): for `θ ≠ 0`,
at every depth `l`, column `c'` and history `h`, the digit `ψ` gives the own response the prescribed value
`w(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})` if and only if `ψ` is the graph rule's digit. -/
theorem graphRule_unique (wt : F → F → F) (θ : F) (hθ : θ ≠ 0) (lamv : Fin 3 → F)
    (zθ : Fin 3 → PowerSeries F) (c' : Fin 3) (h : ℕ → F) (l : ℕ) (ψ : F) :
    (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c' =
        wt (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2 ↔
      ψ = graphRule wt θ lamv zθ c' l h := by
  have hθl : θ ^ l ≠ 0 := pow_ne_zero l hθ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, stAlpha_self, mul_one, graphRule]
  constructor
  · intro hψ
    rw [eq_div_iff hθl, ← hψ]
    ring
  · intro hψ
    rw [hψ]
    field_simp
    ring

end Rule

section Resp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The responses of the graph-rule scramble lie on the graph** (`def:graphrule`): for every column `c'`, every
level `K` and every carry length `1 ≤ l ≤ K`, the own response is `O^{(l)}_{c'} = w(X^{(l)}_{c'+1←c'},
X^{(l)}_{c'+2←c'})`. -/
theorem graph_resp (wt : F → F → F) (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = 3) (θ : F)
    (hθ : θ ≠ 0) (zθ : Fin 3 → PowerSeries F) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin 3 → F) (hlam : ∀ c, lamv c ≠ 0)
    (c' : Fin 3) (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (d0 d1 d2 : F)
    (h0 : IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l c' c' d0)
    (h1 : IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 1) c' d1)
    (h2 : IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 2) c' d2) :
    d0 = wt d1 d2 := by
  set rule := graphRule wt θ lamv zθ with hrule
  have hfacts := ruleMult_facts θ lamv hlam zθ hinj rule
  set g := ruleMult θ lamv zθ rule
  have hg : ∀ c, constantCoeff (g c) ≠ 0 := fun c => (hfacts c).1
  have hlg : ∀ c, lam g zθ c = lamv c := fun c => (hfacts c).2.1
  obtain ⟨hO, hX⟩ := resp_colVec w hw hdeg θ hθ zθ hroot hinj lamv g hg hlg c'
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  set H := ruleHist (rule c') (m + 1) with hH
  set ψ : PowerSeries F := PowerSeries.mk (ruleDigit rule c') with hψ
  have hfree : freeSer g zθ c' = rescale θ ψ := (hfacts c').2.2
  -- the own response
  have e0 : d0 = colVec θ lamv zθ c' (freeSer g zθ c') (m + 1) c' :=
    carryEntry_unique _ _ _ _ _ _ h0 (hO K (m + 1) hl hlK)
  have hβ : stBeta θ lamv zθ c' (fun n => coeff n ψ) (m + 1) = stBeta θ lamv zθ c' H (m + 1) :=
    stBeta_congr θ lamv zθ c' _ _ _ fun n hn => by
      rw [hψ, coeff_mk, hH, ruleHist_eq]; exact (if_pos hn).symm
  have hcoef : coeff (m + 1) ψ = rule c' (m + 1) H := by
    rw [hψ, coeff_mk, ruleDigit_succ rule c' (m + 1) hl]
  have hO' : d0 = wt (graphXi θ lamv zθ c' H (m + 1)).1 (graphXi θ lamv zθ c' H (m + 1)).2 := by
    rw [e0, hfree, colVec_rescale θ lamv zθ hinj c' ψ (m + 1), hβ, hcoef]
    exact (graphRule_unique wt θ hθ lamv zθ c' H (m + 1) _).2 rfl
  -- the crosses at length `m + 1` are entries of the column vector at depth `m`
  have hvec : colVec θ lamv zθ c' (rescale θ (histSer H (m + 1))) m =
      colVec θ lamv zθ c' (freeSer g zθ c') m := by
    rw [hfree, colVec_rescale θ lamv zθ hinj c' _ m, colVec_rescale θ lamv zθ hinj c' _ m]
    have hc : ∀ n, n < m + 1 → coeff n (histSer H (m + 1)) = coeff n ψ := fun n hn => by
      rw [histSer, coeff_mk, if_pos hn, hψ, coeff_mk, hH, ruleHist_eq]; exact if_pos hn
    rw [stBeta_congr θ lamv zθ c' (fun n => coeff n (histSer H (m + 1))) (fun n => coeff n ψ) m
      fun n hn => hc n (by omega), hc m (by omega)]
  have e1 : d1 = colVec θ lamv zθ c' (freeSer g zθ c') m (c' + 1) :=
    carryEntry_unique _ _ _ _ _ _ h1 (hX (c' + 1) (fin3_ne1 c') K m hlK)
  have e2 : d2 = colVec θ lamv zθ c' (freeSer g zθ c') m (c' + 2) :=
    carryEntry_unique _ _ _ _ _ _ h2 (hX (c' + 2) (fin3_ne2 c') K m hlK)
  rw [hO', e1, e2, ← hvec]
  rfl

end Resp

section Cert

/-- `σ_c(-e) = -σ_c(e)`. -/
theorem graphSig_neg {p : ℕ} (wt : ZMod p → ZMod p → ZMod p) (e : Fin 3 → ℤ)
    (ξ : Fin 3 → ZMod p × ZMod p) (c : Fin 3) : graphSig wt (-e) ξ c = -graphSig wt e ξ c := by
  unfold graphSig
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c' _ => ?_
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul]

/-- **`LB^{act}_K ≥ LB(w)`** (proof of `thm:p7`): if every column of every `D(l)` (`1 ≤ l ≤ K`) of a
`(0,3)`-sequence over `𝔽_p` (`p ≥ 5`) lies on the graph of `w` and `LB ≤ LB(w)`, then every term of the
certificate `LB^{act}_K` (`lem:cert`, `j = 1`) is `≥ LB`, and `c(P_{3K}) ≥ min(1, LB)`. -/
theorem graph_cert (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (wt : ZMod p → ZMod p → ZMod p)
    (C : Gen 3 (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (hG : ∀ K l, 1 ≤ l → l ≤ K → ∀ c' (d0 d1 d2 : ZMod p), IsCarryEntry C K 0 l c' c' d0 →
      IsCarryEntry C K 0 l (c' + 1) c' d1 → IsCarryEntry C K 0 l (c' + 2) c' d2 → d0 = wt d1 d2)
    (LB : ℝ) (hLB : GraphLB p wt LB) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ∀ d : Fin 3 → Fin 3 → ZMod p,
      (∀ c c', IsCarryEntry C K 0 (l c') c c' (d c c')) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2)) ∧
    SepAtLevel p 3 K (seqPoint (zcode p) C) (min 1 LB) := by
  have part1 : ∀ e l, IsStep K e l → ∀ d : Fin 3 → Fin 3 → ZMod p,
      (∀ c c', IsCarryEntry C K 0 (l c') c c' (d c c')) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2) := by
    rintro e l ⟨he, hne, hl⟩ d hd
    set ξ : Fin 3 → ZMod p × ZMod p := fun c' => (d (c' + 1) c', d (c' + 2) c') with hξ
    have hcol : ∀ c c', d c c' = graphCol wt (ξ c') c' c := by
      intro c c'
      unfold graphCol
      rcases fin3_cases c c' with h | h | h
      · subst h
        rw [if_pos rfl]
        exact hG K (l c) (hl c).1 (hl c).2 c _ _ _ (hd c c) (hd (c + 1) c) (hd (c + 2) c)
      · subst h
        rw [if_neg (fin3_ne1 c'), if_pos rfl]
      · subst h
        rw [if_neg (fin3_ne2 c'), if_neg (fin3_ne21 c')]
    have hσ : ∀ c, ∑ c', (e c' : ZMod p) * d c c' = graphSig wt e ξ c := fun c => by
      unfold graphSig
      exact Finset.sum_congr rfl fun c' _ => by rw [hcol c c']
    simp only [hσ]
    exact hLB e he hne ξ
  refine ⟨part1, ?_⟩
  have hnet : BlockNet0 (zcode p) C (3 * K) 0 := hseq (3 * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  classical
  let Dr : ℕ → Fin 3 → Fin 3 → ZMod p := fun l c c' =>
    if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists (zcode p) C K hnet 0 l c c') else 0
  have hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c') := by
    intro l h1 h2 c c'
    simp only [Dr, And.intro h1 h2, and_self, dite_true]
    exact Classical.choose_spec (carry_exists (zcode p) C K hnet 0 l c c')
  refine cert_one C K hq hnet Dr hD LB fun e l hst => ?_
  exact part1 e l hst (fun c c' => Dr (l c') c c')
    fun c c' => hD _ (hst.2.2 c').1 (hst.2.2 c').2 c c'

end Cert

section Main

/-- **The graph rule** (`def:graphrule`, the text after it, and the proof of `thm:p7` for any table): let `p ≥ 5` be
prime, `w : 𝔽_p^2 → 𝔽_p` any table, and take any frame of three distinct places (`w` monic of degree `3`, local roots
`z_c(θx)` with `w(z_c(θx)) = θx`), any scale `θ ≠ 0` and any constants `λ_c ≠ 0`. Then
(a) at every depth `l ≥ 1` and for every history there is exactly one digit with
`O^{(l)}_{c'} = w(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})`, the graph rule's;
(b) the graph rule defines a self-similar scramble with the constants `λ_c` (free series = the chosen digits) and a
digital `(0,3)`-sequence over `𝔽_p`;
(c) every column of every `D(l)` lies on the graph `{(w(ξ); ξ)}`;
(d) for every `LB ≤ LB(w)` and every `K ≥ 1`, every term of `LB^{act}_K` is `≥ LB` and `c(P_{3K}) ≥ min(1, LB)`. -/
theorem graph_seq (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (wt : ZMod p → ZMod p → ZMod p)
    (w : (ZMod p)[X]) (hw : w.Monic) (hdeg : w.natDegree = 3) (θ : ZMod p) (hθ : θ ≠ 0)
    (zθ : Fin 3 → PowerSeries (ZMod p)) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin 3 → ZMod p) (hlam : ∀ c, lamv c ≠ 0) :
    (∀ c' (h : ℕ → ZMod p) (l : ℕ), ∃! ψ : ZMod p,
      (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c' =
        wt (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2) ∧
    (∀ c, constantCoeff (ruleMult θ lamv zθ (graphRule wt θ lamv zθ) c) ≠ 0 ∧
      lam (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ c = lamv c ∧
      freeSer (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ c =
        rescale θ (PowerSeries.mk (ruleDigit (graphRule wt θ lamv zθ) c))) ∧
    IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) ∧
    (∀ K l, 1 ≤ l → l ≤ K → ∀ c' (d0 d1 d2 : ZMod p),
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l c' c' d0 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 1) c' d1 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 2) c' d2 →
      d0 = wt d1 d2) ∧
    ∀ LB : ℝ, GraphLB p wt LB → ∀ K : ℕ, 1 ≤ K →
      (∀ e l, IsStep K e l → ∀ d : Fin 3 → Fin 3 → ZMod p,
        (∀ c c', IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 (l c') c c'
          (d c c')) →
        LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2)) ∧
      SepAtLevel p 3 K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ))
        (min 1 LB) := by
  have hfacts := ruleMult_facts θ lamv hlam zθ hinj (graphRule wt θ lamv zθ)
  set g := ruleMult θ lamv zθ (graphRule wt θ lamv zθ)
  have hg : ∀ c, constantCoeff (g c) ≠ 0 := fun c => (hfacts c).1
  have hseq : IsSeq0 (zcode p) (ssGen g zθ) := by
    refine ss_t0 (zcode p) g zθ hinj hg fun c => ?_
    refine left_ne_zero_of_mul (b := placeDer zθ c) ?_
    rw [coeff1_place w hw hdeg θ zθ hroot hinj c]
    exact hθ
  have hG := fun K l hl hlK c' d0 d1 d2 =>
    graph_resp wt w hw hdeg θ hθ zθ hroot hinj lamv hlam c' K l hl hlK d0 d1 d2
  refine ⟨fun c' h l => ⟨graphRule wt θ lamv zθ c' l h,
      (graphRule_unique wt θ hθ lamv zθ c' h l _).2 rfl,
      fun ψ hψ => (graphRule_unique wt θ hθ lamv zθ c' h l ψ).1 hψ⟩,
    hfacts, hseq, hG, fun LB hLB K hK => graph_cert p hp wt _ hseq hG LB hLB K hK⟩

end Main

end GeoSeq
