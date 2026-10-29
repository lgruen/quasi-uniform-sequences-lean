/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Blk
public import GeoSeq.V10_1SignDefs

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 7): the sign-class argument for `thm:block`(iii) at all large primes

The written argument of `thm:block`(c) (diagonal dominance, `dom_LB`) asks every moving coordinate of every step with
two moving axes to be backward. Here a weaker, finitely checkable condition (`SignClass`): every step has a backward
coordinate (`e_i ≠ 0`, `e_i σ_i ≤ 0`) with `|σ_i| ≤ A`, or at least two backward coordinates. Then
`LB(F) ≥ 1 - (A+1)/p` for every prime `p` with `S < p` and `(p - A - 1)² ≤ 2 (p - S - 1)²`, `S` a bound for the
row sums of `|M^{(j)}|` (`sc_LB`). The condition does not depend on `p`; it is certified by ONE kernel evaluation of the
checker `caCheck` at one prime `P` with `s S² + 2A + 3 < 2P` (`ca_signclass`): at such a prime a step violating it would
have `∑_i f_1(e_i, σ_i)² P² ≤ (P - A - 2)² + s S² < (P - A - 1)²`.

* `gap_nonback_le`: a coordinate that is not backward has `f_1(e, t) p ≤ |t|`.
* **`ca_signclass`**, **`sc_LB`**.
-/

namespace GeoSeq

open Finset Polynomial

section Sign
variable {s : ℕ}

lemma stepSig_eq (Mz : ℕ → Fin s → Fin s → ℤ) (e : Fin s → ℤ) (l : Fin s → ℕ) (i : Fin s) :
    stepSig Mz e l i = caSig Mz e l i := rfl

end Sign

section Gap
variable {p : ℕ} [Fact p.Prime]

/-- A coordinate that is not backward (`e = 0`, or `e t > 0`) has `f_1(e, t) p ≤ |t|` (`|t| < p`). -/
lemma gap_nonback_le (e t : ℤ) (he : e = 0 ∨ e = 1 ∨ e = -1) (hnb : ¬ (e ≠ 0 ∧ e * t ≤ 0)) (ht : |t| < p) :
    (gapNum1 p e (t : ZMod p) : ℤ) ≤ |t| := by
  rcases he with rfl | he1
  · by_cases h0 : t = 0
    · subst h0; rw [Int.cast_zero, gapNum1_zero]; simp
    · rw [gapNum1_eq p 0 _ (int_cast_ne t h0 ht)]
      rcases lt_or_gt_of_ne h0 with htn | htp
      · have hv := int_val_neg (p := p) t htn (by rw [abs_lt] at ht; omega)
        have h1 : ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ) - p).natAbs = (|t|).toNat := by
          rw [hv, abs_of_neg htn]; omega
        have h2 : (((min ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ)).natAbs
            ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ) - p).natAbs - 1 : ℕ)) : ℤ) ≤ |t| := by
          have : min ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ)).natAbs
              ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ) - p).natAbs ≤ (|t|).toNat := h1 ▸ min_le_right _ _
          have h3 : ((|t|).toNat : ℤ) = |t| := Int.toNat_of_nonneg (abs_nonneg t)
          omega
        exact h2
      · have hv := int_val_pos (p := p) t htp.le (by rw [abs_lt] at ht; omega)
        have h1 : ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ)).natAbs = (|t|).toNat := by
          rw [hv, abs_of_pos htp]; omega
        have : min ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ)).natAbs
            ((0 : ℤ) * p + (((t : ZMod p)).val : ℤ) - p).natAbs ≤ (|t|).toNat := h1 ▸ min_le_left _ _
        have h3 : ((|t|).toNat : ℤ) = |t| := Int.toNat_of_nonneg (abs_nonneg t)
        omega
  · have hne : e ≠ 0 := by rcases he1 with rfl | rfl <;> norm_num
    have hpos : 0 < e * t := by
      by_contra h; exact hnb ⟨hne, by omega⟩
    rw [gap_fwd e t he1 hpos ht]; omega

end Gap

section Lift
variable {s : ℕ}

/-- `|σ_i| ≤ ∑_c B_{ic}` for every step. -/
lemma caSig_abs_le (Mz : ℕ → Fin s → Fin s → ℤ) (Bd : Fin s → Fin s → ℤ)
    (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (hs : 2 ≤ s) (e : Fin s → ℤ) (l : Fin s → ℕ)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hl : ∀ c, 1 ≤ l c) (i : Fin s) : |stepSig Mz e l i| ≤ ∑ c, Bd i c := by
  unfold stepSig
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul]
  have h1 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
  have h2 := hB (min (l c) (s - 1) - 1) (by have := hl c; omega) i c
  nlinarith [abs_nonneg (e c), abs_nonneg (Mz (min (l c) (s - 1) - 1) i c)]

/-- **The sign-class condition from one kernel evaluation**: if at one prime `P` with `S < P` and
`s S² + 2A + 3 < 2P` every step has a term `≥ 1 - (A+1)/P` (e.g. `caCheck_sound` at `P`), then `SignClass Mz A`. -/
theorem ca_signclass (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (Bd : Fin s → Fin s → ℤ) (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (S A : ℕ)
    (hS : ∀ i, ∑ c, Bd i c ≤ S) (P : ℕ) [Fact P.Prime] (hSP : S < P) (hbig : s * S ^ 2 + 2 * A + 3 < 2 * P)
    (hP : ∀ K e l, IsStep K e l → ((P : ℝ) - A - 1) / P ≤ Real.sqrt (∑ i, ((gapNum1 P (e i)
      (∑ c', (e c' : ZMod P) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / P) ^ 2)) :
    SignClass Mz A := by
  intro K e l hst
  simp only [stepSig_eq]
  obtain ⟨he, hne, hl⟩ := hst
  have h := hP K e l ⟨he, hne, hl⟩
  simp_rw [sig_cast hs Fz Mz hM e l (fun c => (hl c).1)] at h
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin s → ℤ, σ = fun i => caSig Mz e l i := ⟨_, rfl⟩
  have hσi : ∀ i, caSig Mz e l i = σ i := fun i => by rw [hσ]
  simp only [hσi] at h
  set g : Fin s → ℕ := fun i => gapNum1 P (e i) ((σ i : ℤ) : ZMod P) with hg
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hAP : A + 1 ≤ P := by nlinarith
  -- the integer form of the term inequality
  have hint : ((P : ℤ) - A - 1) ^ 2 ≤ ∑ i, ((g i : ℕ) : ℤ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((P : ℝ) - A - 1) / P := div_nonneg (by
      have : ((A : ℕ) : ℝ) + 1 ≤ (P : ℝ) := by exact_mod_cast hAP
      linarith) hP0.le
    have h2 := (Real.le_sqrt h0 (Finset.sum_nonneg fun i _ => sq_nonneg _)).mp h
    have h3 : ∑ i, ((g i : ℝ) / P) ^ 2 = (∑ i, (g i : ℝ) ^ 2) / (P : ℝ) ^ 2 := by
      rw [Finset.sum_div]; simp [div_pow]
    rw [h3, div_pow, div_le_div_iff_of_pos_right (by positivity)] at h2
    exact_mod_cast h2
  by_contra hneg
  simp only [not_or, not_exists, not_and, hσi] at hneg
  obtain ⟨hn1, hn2⟩ := hneg
  have hσS : ∀ i, |σ i| ≤ S := fun i => by
    rw [← hσi]; exact (caSig_abs_le Mz Bd hB hs e l he (fun c => (hl c).1) i).trans (hS i)
  have hσP : ∀ i, |σ i| < P := fun i => by have := hσS i; omega
  have he3 : ∀ i, e i = 0 ∨ e i = 1 ∨ e i = -1 := fun i => by have := he i; omega
  -- at most one backward coordinate, with `|σ| > A`
  set Bk := univ.filter fun i => e i ≠ 0 ∧ e i * σ i ≤ 0 with hBk
  have hcard : Bk.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun i hi i' hi' => ?_
    by_contra hii
    simp only [hBk, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact hn2 i i' hii hi.1 hi.2 hi'.1 hi'.2
  have hterm : ∀ i, ((g i : ℕ) : ℤ) ^ 2 ≤ (S : ℤ) ^ 2 + if i ∈ Bk then ((P : ℤ) - A - 2) ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ Bk
    · rw [if_pos hi]
      simp only [hBk, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hb := gap_back (p := P) (e i) (σ i) ((he3 i).resolve_left hi.1) hi.2 (hσP i)
      have hA := lt_of_not_ge (fun h' => hn1 i hi.1 hi.2 h')
      have hg0 : (0 : ℤ) ≤ (g i : ℤ) := Nat.cast_nonneg _
      have hgi : ((g i : ℕ) : ℤ) = P - |σ i| - 1 := hb
      have : ((g i : ℕ) : ℤ) ≤ (P : ℤ) - A - 2 := by rw [hgi]; omega
      nlinarith [sq_nonneg (S : ℤ)]
    · rw [if_neg hi, add_zero]
      have hnb : ¬ (e i ≠ 0 ∧ e i * σ i ≤ 0) := fun h' => hi (by
        simp only [hBk, Finset.mem_filter, Finset.mem_univ, true_and]; exact h')
      have h1 := gap_nonback_le (p := P) (e i) (σ i) (he3 i) hnb (hσP i)
      have hg0 : (0 : ℤ) ≤ (g i : ℤ) := Nat.cast_nonneg _
      have h2 : ((g i : ℕ) : ℤ) ≤ S := h1.trans (hσS i)
      nlinarith
  have hsum : ∑ i, ((g i : ℕ) : ℤ) ^ 2 ≤ s * (S : ℤ) ^ 2 + Bk.card * ((P : ℤ) - A - 2) ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  have hc : (Bk.card : ℤ) ≤ 1 := by exact_mod_cast hcard
  have hbig' : (s : ℤ) * (S : ℤ) ^ 2 + 2 * A + 3 < 2 * P := by exact_mod_cast hbig
  have hsq : (0 : ℤ) ≤ ((P : ℤ) - A - 2) ^ 2 := sq_nonneg _
  nlinarith

end Lift

section SC
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **The sign-class bound** (generalizes the diagonal-dominance argument `dom_LB`): under `SignClass Mz A`, for every
prime `p` with `S < p` (`S` bounds the row sums of `|M^{(j)}|`), `A ≤ S` and `(p - A - 1)² ≤ 2 (p - S - 1)²`, every step
has a term `≥ 1 - (A+1)/p`, i.e. `LB(F) ≥ 1 - (A+1)/p`. -/
theorem sc_LB (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (Bd : Fin s → Fin s → ℤ) (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (S A : ℕ)
    (hS : ∀ i, ∑ c, Bd i c ≤ S) (hSp : S < p) (hAS : A ≤ S)
    (hq : ((p : ℤ) - A - 1) ^ 2 ≤ 2 * ((p : ℤ) - S - 1) ^ 2) (hcl : SignClass Mz A) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2) := by
  intro e l hst
  obtain ⟨he, hne, hl⟩ := hst
  simp_rw [sig_cast hs Fz Mz hM e l (fun c => (hl c).1)]
  apply LB_of_sq
  have hσS : ∀ i, |caSig Mz e l i| ≤ S := fun i =>
    (caSig_abs_le Mz Bd hB hs e l he (fun c => (hl c).1) i).trans (hS i)
  have he3 : ∀ i, e i = 0 ∨ e i = 1 ∨ e i = -1 := fun i => by have := he i; omega
  have hback : ∀ i, e i ≠ 0 → e i * caSig Mz e l i ≤ 0 →
      ((gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) : ℕ) : ℤ) = p - |caSig Mz e l i| - 1 := fun i h1 h2 =>
    gap_back (p := p) (e i) _ ((he3 i).resolve_left h1) h2 (by have := hσS i; omega)
  have hcl' := hcl K e l ⟨he, hne, hl⟩
  simp only [stepSig_eq] at hcl'
  rcases hcl' with ⟨i, hi1, hi2, hi3⟩ | ⟨i, i', hii, hi1, hi2, hi1', hi2'⟩
  · have hle := Finset.single_le_sum
      (f := fun i => ((gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) : ℕ) : ℤ) ^ 2)
      (fun i _ => sq_nonneg _) (mem_univ i)
    rw [hback i hi1 hi2] at hle
    have hx : (p : ℤ) - A - 1 ≤ p - |caSig Mz e l i| - 1 := by linarith
    have h0 : (0 : ℤ) ≤ p - A - 1 := by have := hσS i; omega
    nlinarith [mul_le_mul hx hx h0 (h0.trans hx)]
  · have hle := Finset.add_le_sum
      (f := fun i => ((gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) : ℕ) : ℤ) ^ 2)
      (fun i _ => sq_nonneg _) (mem_univ i) (mem_univ i') hii
    rw [hback i hi1 hi2, hback i' hi1' hi2'] at hle
    have hx : (p : ℤ) - S - 1 ≤ p - |caSig Mz e l i| - 1 := by linarith [hσS i]
    have hy : (p : ℤ) - S - 1 ≤ p - |caSig Mz e l i'| - 1 := by linarith [hσS i']
    have h0 : (0 : ℤ) ≤ p - S - 1 := by omega
    nlinarith [mul_le_mul hx hx h0 (h0.trans hx), mul_le_mul hy hy h0 (h0.trans hy)]

end SC

end GeoSeq
