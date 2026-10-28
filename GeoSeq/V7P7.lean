/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7P7a
public import GeoSeq.V7P7b
public import GeoSeq.V7P7c
public import GeoSeq.V2Cauchy
public import GeoSeq.Mesh
public import GeoSeq.V1Aux

@[expose] public section

/-!
# GeoSeq stage V7: `thm:p7` (base seven in dimension three)

* **`p7_LB`**: `LB(w) ≥ 1/7` for the table of `tab:p7` (13 steps up to sign, kernel-checked in
  `V7P7a/b/c`; the term is invariant under `e ↦ -e`); **`p7_LB_eq`**: `LB(w) = 1/7` exactly (attained by the
  axis step `e = (1,0,0)` with `ξ = (0,1)`, as in the proof of `thm:p7`).
* **`p7`** (`thm:p7`): for every frame of three distinct places in `𝔽_7`, every scale `θ ≠ 0` and all constants
  `λ_c ≠ 0`, the graph rule of `w` gives a quasi-uniform digital `(0,3)`-sequence over `𝔽_7` with
  `c(P_{3K}) ≥ 1/7` for every `K ≥ 1`.
* **`p7_exists`**: non-vacuity (the Faure frame, `θ = 1`, `λ = 1`): a sequence `QUSep (zcode 7) 3 C (1/7)` exists.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

lemma p7_chk_all (a b c : ℤ) (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hc : c = -1 ∨ c = 0 ∨ c = 1) (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    p7chk (p7code a) (p7code b) (p7code c) = true ∨
      p7chk (p7code (-a)) (p7code (-b)) (p7code (-c)) = true := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := p7chk_small
  have t1 := p7chk_111
  have t2 := p7chk_116
  have t3 := p7chk_161
  have t4 := p7chk_166
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
    simp_all [p7code]

/-- **`LB(w) ≥ 1/7`** for the table `w` of `tab:p7` (the finite statement of the proof of `thm:p7`: no step and no
choice of the `ξ^{(c')}` makes every term vanish). -/
theorem p7_LB : GraphLB 7 wP7 (1 / 7) := by
  intro e he hne ξ
  have he' : ∀ c, e c = -1 ∨ e c = 0 ∨ e c = 1 := fun c => by have := he c; omega
  have hne' : ¬(e 0 = 0 ∧ e 1 = 0 ∧ e 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    obtain ⟨c, hc⟩ := hne
    fin_cases c <;> simp_all
  have key : ∃ c, gapNum1 7 (e c) (graphSig wP7 e ξ c) ≠ 0 := by
    rcases p7_chk_all (e 0) (e 1) (e 2) (he' 0) (he' 1) (he' 2) hne' with h | h
    · exact p7chk_sound e he' h ξ
    · obtain ⟨c, hc⟩ := p7chk_sound (-e) (fun c => by rcases he' c with h | h | h <;> simp [h]) h ξ
      refine ⟨c, ?_⟩
      rwa [graphSig_neg, Pi.neg_apply, gapNum1_neg] at hc
  obtain ⟨c, hc⟩ := key
  set g := gapNum1 7 (e c) (graphSig wP7 e ξ c) with hgdef
  have hg : (1 : ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
  calc (1 / 7 : ℝ) ≤ (g : ℝ) / (7 : ℕ) := by push_cast; linarith
    _ = Real.sqrt (((g : ℝ) / (7 : ℕ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
        (f := fun c => ((gapNum1 7 (e c) (graphSig wP7 e ξ c) : ℝ) / (7 : ℕ)) ^ 2)
        (fun c _ => sq_nonneg _) (Finset.mem_univ c))

lemma p7_axis_sig : ∀ c, graphSig wP7 ![1, 0, 0] (fun _ => (0, 1)) c = ![2, 0, 1] c := by decide

/-- **`LB(w) = 1/7`** (proof of `thm:p7`): `1/7` is the largest `LB` with `LB ≤ LB(w)`; it is attained by the axis
step `e = (1, 0, 0)` with `ξ = (0, 1)`. -/
theorem p7_LB_eq : IsGreatest {LB : ℝ | GraphLB 7 wP7 LB} (1 / 7) := by
  refine ⟨p7_LB, fun LB hLB => ?_⟩
  have h := hLB ![1, 0, 0] (fun c => by fin_cases c <;> simp) ⟨0, by simp⟩ (fun _ => (0, 1))
  simp only [p7_axis_sig, Fin.sum_univ_three] at h
  have g0 : gapNum1 7 ((![1, 0, 0] : Fin 3 → ℤ) 0) ((![2, 0, 1] : Fin 3 → ZMod 7) 0) = 1 := by
    rw [show ((![1, 0, 0] : Fin 3 → ℤ) 0) = 1 from rfl, f1_one_val]; decide
  have g1 : gapNum1 7 ((![1, 0, 0] : Fin 3 → ℤ) 1) ((![2, 0, 1] : Fin 3 → ZMod 7) 1) = 0 := by
    rw [show ((![1, 0, 0] : Fin 3 → ℤ) 1) = 0 from rfl, f1_zero_val]; decide
  have g2 : gapNum1 7 ((![1, 0, 0] : Fin 3 → ℤ) 2) ((![2, 0, 1] : Fin 3 → ZMod 7) 2) = 0 := by
    rw [show ((![1, 0, 0] : Fin 3 → ℤ) 2) = 0 from rfl, f1_zero_val]; decide
  rw [g0, g1, g2] at h
  have e1 : Real.sqrt ((((1 : ℕ) : ℝ) / (7 : ℕ)) ^ 2 + (((0 : ℕ) : ℝ) / (7 : ℕ)) ^ 2 +
      (((0 : ℕ) : ℝ) / (7 : ℕ)) ^ 2) = 1 / 7 := by
    rw [show (((1 : ℕ) : ℝ) / (7 : ℕ)) ^ 2 + (((0 : ℕ) : ℝ) / (7 : ℕ)) ^ 2 +
      (((0 : ℕ) : ℝ) / (7 : ℕ)) ^ 2 = (1 / 7) ^ 2 by push_cast; ring]
    exact Real.sqrt_sq (by norm_num)
  rw [e1] at h
  exact h

/-- **`thm:p7`** (base seven). Let `w` be the table of `tab:p7`. For every frame of three distinct places in `𝔽_7`
(`w` monic of degree `3`, local roots `z_c(θx)` with `w(z_c(θx)) = θx`), every scale `θ ≠ 0` and all constants
`λ_c ≠ 0`: the graph rule is well defined (at every depth and history exactly one digit puts the own response on the
graph), it defines a self-similar scramble with the constants `λ_c`, all responses lie on the graph, and the sequence
is a quasi-uniform digital `(0,3)`-sequence over `𝔽_7` with `c(P_{3K}) ≥ 1/7` for every `K ≥ 1` (mesh ratio
`≤ √3 · 7 / (1/7)` along all `N ≥ 2`, `lem:prefix`). -/
theorem p7 (w : (ZMod 7)[X]) (hw : w.Monic) (hdeg : w.natDegree = 3) (θ : ZMod 7) (hθ : θ ≠ 0)
    (zθ : Fin 3 → PowerSeries (ZMod 7)) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin 3 → ZMod 7) (hlam : ∀ c, lamv c ≠ 0) :
    (∀ c' (h : ℕ → ZMod 7) (l : ℕ), ∃! ψ : ZMod 7,
      (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c' =
        wP7 (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2) ∧
    (∀ c, constantCoeff (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ) c) ≠ 0 ∧
      lam (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ c = lamv c) ∧
    (∀ K l, 1 ≤ l → l ≤ K → ∀ c' (d0 d1 d2 : ZMod 7),
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) K 0 l c' c' d0 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) K 0 l (c' + 1) c' d1 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) K 0 l (c' + 2) c' d2 →
      d0 = wP7 d1 d2) ∧
    QUSep (zcode 7) 3 (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) (1 / 7) := by
  obtain ⟨ha, hfacts, hseq, hG, hcert⟩ :=
    graph_seq 7 (by norm_num) wP7 w hw hdeg θ hθ zθ hroot hinj lamv hlam
  have hsep : ∀ K : ℕ, 1 ≤ K → SepAtLevel 7 3 K
      (seqPoint (zcode 7) (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ)) (1 / 7) := by
    intro K hK
    have := (hcert (1 / 7) p7_LB K hK).2
    rwa [min_eq_right (by norm_num)] at this
  refine ⟨ha, fun c => ⟨(hfacts c).1, (hfacts c).2.1⟩, hG, hseq, hsep, fun N hN => ?_⟩
  have := prefix_mesh (zcode 7) _ (by norm_num) (by norm_num) hseq (1 / 7) (by norm_num) hsep N hN
  simpa using this

/-- Non-vacuity of `thm:p7`: on the Faure frame `z(z-1)(z-2)` (`θ = 1`, `λ = 1`) the graph rule of `tab:p7` gives a
quasi-uniform digital `(0,3)`-sequence over `𝔽_7` with `c(P_{3K}) ≥ 1/7` for every `K ≥ 1`. -/
theorem p7_exists : ∃ C : Gen 3 (ZMod 7), QUSep (zcode 7) 3 C (1 / 7) := by
  obtain ⟨zθ, hroot, hplace⟩ := faure_roots_exist 3 7 (by norm_num) 1
  have hinj : Function.Injective (ssPlace zθ) := by
    intro a b hab
    simp only [ssPlace, hplace] at hab
    revert a b; decide
  exact ⟨_, (p7 (faureW 3 7) (faureW_monic 3 7) (faureW_natDegree 3 7) 1 one_ne_zero zθ hroot hinj
    (fun _ => 1) (fun _ => one_ne_zero)).2.2.2⟩

end GeoSeq
