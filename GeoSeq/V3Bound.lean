/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Mono

@[expose] public section

/-!
# GeoSeq stage V3: the estimate `Γ/p ≤ F(u)` (first half of `lem:MRbound`)

`mr_bound_u`: for every real `u > u_min` with `p = Q_s^s u^s` and step factors with `|h_t - γ_t u| ≤ 1/2`,
the cost of `MR(s,p,h)` satisfies `Γ/p ≤ F(u)` — provided `F_0(u) ≤ 1` (equivalently, together with the
other hypotheses, the fast row of (MR2) is never truncated: `2ν_{0j} + 1 ≤ p` for every column; see the
review: the Lean recursion `mrN` uses truncated subtraction in `ℕ`, and the paper's estimate
`N ≤ (p-1)/ν_{0j}` after the fast row uses `p ≥ 2ν_{0j} + 1`). Proof as in the paper: `ν^- ≤ ν ≤ ν^+`,
`⌈x⌉ ≤ x + 1` along the recursion gives `N ≤ p η_t(j)` after row `t`, `⌈(x-1)/2⌉ ≤ x/2`, and summing.
-/

namespace GeoSeq

open Finset

lemma cdiv_le_real (a b : ℕ) (hb : 1 ≤ b) : (cdiv a b : ℝ) ≤ ((a : ℝ) + b - 1) / b := by
  unfold cdiv
  have h := Nat.cast_div_le (α := ℝ) (m := a + b - 1) (n := b)
  have e : ((a + b - 1 : ℕ) : ℝ) = (a : ℝ) + b - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e] at h
  exact h

lemma cdiv_sub_one_two_le (x : ℕ) : (cdiv (x - 1) 2 : ℝ) ≤ (x : ℝ) / 2 := by
  rcases x with _ | x
  · simp [cdiv]
  · have := cdiv_le_real x 2 (by norm_num)
    simp only [Nat.add_sub_cancel]
    refine this.trans (le_of_eq ?_)
    push_cast; ring

section Bound

variable (s p : ℕ) (h : ℕ → ℕ) (u : ℝ)

/-- **`lem:MRbound`, first part** (real parameter `u`): if `u > u_min`, `p = Q_s^s u^s` (`p ≥ 1`), the step
factors satisfy `|h_t - γ_t u| ≤ 1/2` (`1 ≤ t ≤ n`) and `F_0(u) ≤ 1`, then `Γ/p ≤ F(u)`. -/
theorem mr_bound_u (hs : 2 ≤ s) (hp : 1 ≤ p) (hu : (mrUmin s : ℝ) < u) (hpu : (p : ℝ) = mrPu s u)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → |(h t : ℝ) - mrGamma s t * u| ≤ 1 / 2)
    (hF0 : mrFrow s 0 u ≤ 1) :
    (mrCost s p h : ℝ) / p ≤ mrF s u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hgu : ∀ i, 1 ≤ i → i ≤ s - 1 → 0 < (mrGamma s i : ℝ) * u - 1 / 2 := fun i h1 h2 => by
    have := mrGamma_umin s i hs h1 h2
    have : (0 : ℝ) < mrGamma s i := by exact_mod_cast mrGamma_pos s i hs h1 h2
    nlinarith
  have hhb : ∀ t, 1 ≤ t → t ≤ s - 1 →
      (mrGamma s t : ℝ) * u - 1 / 2 ≤ h t ∧ (h t : ℝ) ≤ (mrGamma s t : ℝ) * u + 1 / 2 := fun t h1 h2 => by
    have := abs_le.mp (hh t h1 h2); constructor <;> linarith [this.1, this.2]
  have hh1 : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t := fun t h1 h2 => by
    have := (hhb t h1 h2).1
    have := hgu t h1 h2
    have : (0 : ℝ) < h t := by linarith
    exact_mod_cast this
  -- `ν^- ≤ ν ≤ ν^+`
  have hnu : ∀ t j, t < j → j < s → 0 < mrNuM s t j u ∧ mrNuM s t j u ≤ (mrNu s h t j : ℝ) ∧
      (mrNu s h t j : ℝ) ≤ mrNuP s t j u := by
    intro t j htj hj
    have hm : (0 : ℝ) < mrMuBar s t j := by exact_mod_cast mrMuBar_pos' s t j hs htj hj
    have hcast : (mrNu s h t j : ℝ) = (mrMuBar s t j : ℝ) * ∏ i ∈ Ioc t j, (h i : ℝ) := by
      unfold mrNu hprod mrMuBar; push_cast; rfl
    have hI : ∀ i ∈ Ioc t j, 1 ≤ i ∧ i ≤ s - 1 := fun i hi => by
      have := mem_Ioc.mp hi; constructor <;> omega
    refine ⟨mul_pos hm (prod_pos fun i hi => hgu i (hI i hi).1 (hI i hi).2), ?_, ?_⟩
    · rw [hcast]; unfold mrNuM
      exact mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i hi => (hgu i (hI i hi).1 (hI i hi).2).le)
        fun i hi => (hhb i (hI i hi).1 (hI i hi).2).1) hm.le
    · rw [hcast]; unfold mrNuP
      exact mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
        fun i hi => (hhb i (hI i hi).1 (hI i hi).2).2) hm.le
  -- the fast row is not truncated
  have htr : ∀ j, 0 < j → j < s → 2 * mrNu s h 0 j + 1 ≤ p := by
    intro j hj0 hj
    have hP : (0 : ℝ) < mrPu s u := hpu ▸ hp0
    have h1 : 2 * ∑ j ∈ Ioo 0 s, mrNuP s 0 j u + 1 ≤ mrPu s u := by
      have := hF0; unfold mrFrow at this; rw [ite_eq_left_of_eq_true _ _ (eq_self 0), div_le_one hP] at this; exact this
    have h2 : mrNuP s 0 j u ≤ ∑ j ∈ Ioo 0 s, mrNuP s 0 j u :=
      single_le_sum (f := fun j => mrNuP s 0 j u) (fun k hk =>
        ((hnu 0 k (mem_Ioo.mp hk).1 (mem_Ioo.mp hk).2).1.trans_le
          ((hnu 0 k (mem_Ioo.mp hk).1 (mem_Ioo.mp hk).2).2.1.trans
            (hnu 0 k (mem_Ioo.mp hk).1 (mem_Ioo.mp hk).2).2.2)).le) (mem_Ioo.mpr ⟨hj0, hj⟩)
    have h3 := (hnu 0 j hj0 hj).2.2
    have : ((2 * mrNu s h 0 j + 1 : ℕ) : ℝ) ≤ p := by push_cast; linarith
    exact_mod_cast this
  -- `N ≤ p η_t(j)` after row `t`
  have hN : ∀ j, 0 < j → j < s → ∀ t, t < j → (mrN s p h j t : ℝ) ≤ p * mrEta s t j u := by
    intro j hj0 hj t
    induction t with
    | zero =>
      intro _
      have hν := mrNu_pos s hs h hh1 0 j hj0 hj
      have ht := htr j hj0 hj
      obtain ⟨hm0, hm1, -⟩ := hnu 0 j hj0 hj
      have hc := cdiv_le_real (p - 2 * mrNu s h 0 j - 1) (mrNu s h 0 j) hν
      have e : ((p - 2 * mrNu s h 0 j - 1 : ℕ) : ℝ) = p - 2 * (mrNu s h 0 j : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e] at hc
      have hν' : (1 : ℝ) ≤ mrNu s h 0 j := by exact_mod_cast hν
      simp only [mrN, mrEta, zero_add, sum_range_one]
      push_cast
      have key : (1 : ℝ) + ((p : ℝ) - 2 * mrNu s h 0 j - 1 + mrNu s h 0 j - 1) / mrNu s h 0 j ≤
          p / mrNu s h 0 j := by
        rw [← sub_nonneg]
        have : (p : ℝ) / mrNu s h 0 j - (1 + ((p : ℝ) - 2 * mrNu s h 0 j - 1 + mrNu s h 0 j - 1) /
          mrNu s h 0 j) = 2 / mrNu s h 0 j := by field_simp; ring
        rw [this]; positivity
      calc (1 : ℝ) + (cdiv (p - 2 * mrNu s h 0 j - 1) (mrNu s h 0 j) : ℝ)
          ≤ 1 + ((p : ℝ) - 2 * mrNu s h 0 j - 1 + mrNu s h 0 j - 1) / mrNu s h 0 j := by linarith
        _ ≤ p / mrNu s h 0 j := key
        _ ≤ p / mrNuM s 0 j u := div_le_div_of_nonneg_left hp0.le hm0 hm1
        _ = p * (1 / mrNuM s 0 j u) := by ring
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hN1 := mrN_pos (s := s) (p := p) (h := h) hs hp hh1 j hj t (by omega)
      have hν := mrNu_pos s hs h hh1 (t + 1) j ht hj
      obtain ⟨hm0, hm1, -⟩ := hnu (t + 1) j ht hj
      have hc := cdiv_le_real p (mrNu s h (t + 1) j) hν
      have hν' : (1 : ℝ) ≤ mrNu s h (t + 1) j := by exact_mod_cast hν
      simp only [mrN]
      rw [Nat.cast_add, Nat.cast_sub hN1, mrEta, sum_range_succ, ← mrEta, mul_add]
      push_cast
      have key : ((p : ℝ) + mrNu s h (t + 1) j - 1) / mrNu s h (t + 1) j - 1 ≤ p / mrNu s h (t + 1) j := by
        rw [← sub_nonneg]
        have : (p : ℝ) / mrNu s h (t + 1) j - (((p : ℝ) + mrNu s h (t + 1) j - 1) /
          mrNu s h (t + 1) j - 1) = 1 / mrNu s h (t + 1) j := by field_simp; ring
        rw [this]; positivity
      have h4 : (p : ℝ) / mrNu s h (t + 1) j ≤ p * (1 / mrNuM s (t + 1) j u) := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_left hp0.le hm0 hm1
      linarith
  -- row bounds
  have hP : mrPu s u = p := hpu.symm
  have hrow : ∀ c, c < s → ((2 * mrB s p h c + mrM s p h c : ℕ) : ℝ) ≤ p * mrFrow s c u := by
    intro c hc
    by_cases hc0 : c = 0
    · subst hc0
      unfold mrFrow
      rw [ite_eq_left_of_eq_true _ _ (eq_self 0), hP, mul_div_cancel₀ _ hp0.ne']
      simp only [mrB, mrM, mrBx, ↓reduceIte]
      push_cast
      have : ∑ j ∈ Ioo 0 s, (mrNu s h 0 j : ℝ) ≤ ∑ j ∈ Ioo 0 s, mrNuP s 0 j u :=
        sum_le_sum fun j hj => (hnu 0 j (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2).2.2
      linarith
    · unfold mrFrow
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc0), mul_add]
      have hM : (mrM s p h c : ℝ) ≤ p * mrEta s (c - 1) c u := by
        unfold mrM; rw [ite_eq_right_of_eq_false _ _ (eq_false hc0)]; exact hN c (by omega) hc (c - 1) (by omega)
      have hB : (mrB s p h c : ℝ) ≤ ∑ j ∈ Ioo c s,
          p * max (mrNuP s c j u / mrPu s u) (mrEta s (c - 1) j u * mrNuP s c j u / 2) := by
        unfold mrB; push_cast
        refine sum_le_sum fun j hj => ?_
        have hcj := (mem_Ioo.mp hj).1
        have hjs := (mem_Ioo.mp hj).2
        obtain ⟨hm0, hm1, hm2⟩ := hnu c j hcj hjs
        rw [mul_max_of_nonneg _ _ hp0.le, hP, mul_div_cancel₀ _ hp0.ne']
        unfold mrBx; rw [ite_eq_right_of_eq_false _ _ (eq_false hc0)]
        push_cast
        refine max_le_max hm2 ((cdiv_sub_one_two_le _).trans ?_)
        push_cast
        have hNc := hN j (by omega) hjs (c - 1) (by omega)
        have hN0 : (0 : ℝ) ≤ mrN s p h j (c - 1) := Nat.cast_nonneg _
        have : (mrN s p h j (c - 1) : ℝ) * mrNu s h c j ≤ p * mrEta s (c - 1) j u * mrNuP s c j u :=
          mul_le_mul hNc hm2 (Nat.cast_nonneg _) (by
            have : 0 ≤ mrEta s (c - 1) j u := le_trans hN0 hNc |> fun h' => by
              exact nonneg_of_mul_nonneg_right (by linarith) hp0
            positivity)
        linarith
      push_cast
      rw [mul_left_comm, mul_sum]
      linarith
  -- the cost
  have hne : (range s).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup (range s) hne (fun c => 2 * mrB s p h c + mrM s p h c)
  have hcs := mem_range.mp hc
  rw [div_le_iff₀ hp0]
  unfold mrCost
  rw [hce]
  refine (hrow c hcs).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hp0.le
  unfold mrF
  rw [dite_eq_left_of_eq_true (eq_true hne)]
  exact Finset.le_sup' (fun c => mrFrow s c u) hc

end Bound

end GeoSeq
