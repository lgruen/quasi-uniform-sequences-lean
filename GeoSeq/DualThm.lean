/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.DualPoly

@[expose] public section

/-!
# GeoSeq stage S10: `thm:dual`, part 3: the criterion (a)

* `dual_kernel`: under the three conditions (distinct places, distinct parameters, points `(a_c, ξ_c)`
  not collinear), every composition `d` of every `m` passes the kernel test — the classical Faure
  argument over the dual numbers: `(z-a_c)^{e_c}` divides `V_0` and `V_1`, so `V_i = W_E V_i'`, the degree
  bounds leave `V_0' = ν_0 + ν_2 z`, `V_1' = ν_1`, and the coordinates with `d_c` odd give
  `ν_0 + ν_2 a_c + ξ_c ν_1 = 0` (the factor `ϑ_c ≠ 0` cancels).
* **`dual_a`** (`thm:dual`(a), any finite field): `eq:dual` is a `(0,3)`-sequence iff the three conditions
  hold; **`dual_fail`**: if a condition fails, already `P_2` or `P_3` is not a net.
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F]

lemma solve2 {ν0 ν1 x y : F} (hxy : x ≠ y) (hx : ν0 + x * ν1 = 0) (hy : ν0 + y * ν1 = 0) :
    ν0 = 0 ∧ ν1 = 0 := by
  have h1 : (x - y) * ν1 = 0 := by linear_combination hx - hy
  have hν1 : ν1 = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hxy)
  refine ⟨?_, hν1⟩
  rw [hν1, mul_zero, add_zero] at hx; exact hx

lemma solve3 (a ξ : Fin 3 → F) (hdet : (a 1 - a 0) * (ξ 2 - ξ 0) - (a 2 - a 0) * (ξ 1 - ξ 0) ≠ 0)
    {ν0 ν1 ν2 : F} (h : ∀ c, ν0 + ν2 * a c + ξ c * ν1 = 0) : ν0 = 0 ∧ ν1 = 0 ∧ ν2 = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have e2 : ν2 * ((a 1 - a 0) * (ξ 2 - ξ 0) - (a 2 - a 0) * (ξ 1 - ξ 0)) = 0 := by
    linear_combination (ξ 2 - ξ 0) * (h1 - h0) - (ξ 1 - ξ 0) * (h2 - h0)
  have e1 : ν1 * ((a 1 - a 0) * (ξ 2 - ξ 0) - (a 2 - a 0) * (ξ 1 - ξ 0)) = 0 := by
    linear_combination (a 1 - a 0) * (h2 - h0) - (a 2 - a 0) * (h1 - h0)
  have hν2 := (mul_eq_zero.1 e2).resolve_right hdet
  have hν1 := (mul_eq_zero.1 e1).resolve_right hdet
  refine ⟨?_, hν1, hν2⟩
  rw [hν1, hν2] at h0; simpa using h0

/-- **The kernel test for `eq:dual`** (`s = 3`, any field): under the three conditions every index
vector whose first `d_c` digits vanish in every coordinate, `∑ d_c = m`, is zero. -/
theorem dual_kernel (a ξ : Fin 3 → F) (ha : Function.Injective a) (hξ : Function.Injective ξ)
    (hdet : (a 1 - a 0) * (ξ 2 - ξ 0) - (a 2 - a 0) * (ξ 1 - ξ 0) ≠ 0)
    (m : ℕ) (d : Fin 3 → ℕ) (hd : ∑ c, d c = m) (V : Fin m → F)
    (hV : ∀ c, ∀ n < d c, vecDigit (dualGen a ξ) V c n = 0) : V = 0 := by
  have hT1 : ∀ c, ∀ i < d c / 2, (taylor (a c) (dualP1 V)).coeff i = 0 := fun c i hi => by
    rw [← dual_digit_odd a ξ V c i]; exact hV c _ (by omega)
  have hT0 : ∀ c, ∀ i < d c / 2, (taylor (a c) (dualP0 V)).coeff i = 0 := fun c i hi => by
    have h := hV c (2 * i) (by omega)
    rw [dual_digit_even, map_add, taylor_mul, taylor_C, coeff_add, coeff_C_mul, hT1 c i hi,
      mul_zero, add_zero] at h
    exact h
  have hTf : ∀ c, d c % 2 = 1 →
      (taylor (a c) (dualP0 V + C (ξ c) * dualP1 V)).coeff (d c / 2) = 0 := fun c hc => by
    rw [← dual_digit_even]; exact hV c _ (by omega)
  set W : F[X] := ∏ c, (X - C (a c)) ^ (d c / 2) with hWdef
  have hcop : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).Pairwise
      (Function.onFun IsCoprime fun c => (X - C (a c)) ^ (d c / 2)) := by
    intro c _ c' _ hcc'
    exact ((pairwise_coprime_X_sub_C ha) hcc').pow
  obtain ⟨Q0, hQ0⟩ : W ∣ dualP0 V :=
    Finset.prod_dvd_of_coprime hcop fun c _ => dvd_of_taylor _ _ _ (hT0 c)
  obtain ⟨Q1, hQ1⟩ : W ∣ dualP1 V :=
    Finset.prod_dvd_of_coprime hcop fun c _ => dvd_of_taylor _ _ _ (hT1 c)
  set E := ∑ c, d c / 2 with hE
  set Fm := ∑ c, d c % 2 with hFm
  have hm : m = 2 * E + Fm := by
    rw [hE, hFm, ← hd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    omega
  have hFm3 : Fm ≤ 3 := by
    rw [hFm, Fin.sum_univ_three]
    have := Nat.mod_lt (d 0) two_pos; have := Nat.mod_lt (d 1) two_pos
    have := Nat.mod_lt (d 2) two_pos; omega
  have hWm : W.Monic := monic_prod_of_monic _ _ fun c _ => (monic_X_sub_C _).pow _
  have hWdeg : W.natDegree = E := by
    rw [hWdef, natDegree_prod_of_monic _ _ (fun c _ => (monic_X_sub_C _).pow _)]
    simp [natDegree_pow, natDegree_X_sub_C]
    exact hE.symm
  have hQ0c : ∀ j, (Fm + 1) / 2 ≤ j → Q0.coeff j = 0 := by
    intro j hj
    by_contra hne
    have hQ0ne : Q0 ≠ 0 := fun h => hne (by rw [h, coeff_zero])
    have hjd : j ≤ Q0.natDegree := le_natDegree_of_ne_zero hne
    have hPne : dualP0 V ≠ 0 := by rw [hQ0]; exact mul_ne_zero hWm.ne_zero hQ0ne
    have hP0deg : (dualP0 V).natDegree = E + Q0.natDegree := by
      rw [hQ0, natDegree_mul hWm.ne_zero hQ0ne, hWdeg]
    have hlc : (dualP0 V).coeff (dualP0 V).natDegree ≠ 0 := by
      rw [coeff_natDegree]; exact leadingCoeff_ne_zero.2 hPne
    rw [dualP0_coeff, dif_neg (by omega)] at hlc
    exact hlc rfl
  have hQ1c : ∀ j, Fm / 2 ≤ j → Q1.coeff j = 0 := by
    intro j hj
    by_contra hne
    have hQ1ne : Q1 ≠ 0 := fun h => hne (by rw [h, coeff_zero])
    have hjd : j ≤ Q1.natDegree := le_natDegree_of_ne_zero hne
    have hPne : dualP1 V ≠ 0 := by rw [hQ1]; exact mul_ne_zero hWm.ne_zero hQ1ne
    have hP1deg : (dualP1 V).natDegree = E + Q1.natDegree := by
      rw [hQ1, natDegree_mul hWm.ne_zero hQ1ne, hWdeg]
    have hlc : (dualP1 V).coeff (dualP1 V).natDegree ≠ 0 := by
      rw [coeff_natDegree]; exact leadingCoeff_ne_zero.2 hPne
    rw [dualP1_coeff, dif_neg (by omega)] at hlc
    exact hlc rfl
  -- the conditions of the coordinates with `d_c` odd
  have hval : ∀ c, d c % 2 = 1 → (Q0 + C (ξ c) * Q1).eval (a c) = 0 := by
    intro c hc
    have h := hTf c hc
    have hsplit : W = (X - C (a c)) ^ (d c / 2) *
        ∏ c'' ∈ univ.erase c, (X - C (a c'')) ^ (d c'' / 2) :=
      (Finset.mul_prod_erase univ _ (Finset.mem_univ c)).symm
    rw [hQ0, hQ1, show W * Q0 + C (ξ c) * (W * Q1) = (X - C (a c)) ^ (d c / 2) *
        ((∏ c'' ∈ univ.erase c, (X - C (a c'')) ^ (d c'' / 2)) * (Q0 + C (ξ c) * Q1)) by
      rw [hsplit]; ring, taylor_coeff_split, eval_mul] at h
    have hU : (∏ c'' ∈ univ.erase c, (X - C (a c'')) ^ (d c'' / 2)).eval (a c) ≠ 0 := by
      rw [eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun c'' hc'' => ?_
      rw [eval_pow]
      refine pow_ne_zero _ ?_
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.2 (ha.ne (Finset.mem_erase.1 hc'').1.symm)
    exact (mul_eq_zero.1 h).resolve_left hU
  -- `Q0 = ν0 + ν2 X`, `Q1 = ν1`
  set ν0 := Q0.coeff 0
  set ν2 := Q0.coeff 1
  set ν1 := Q1.coeff 0
  have hQ0f : Q0 = C ν0 + C ν2 * X := by
    ext j
    rcases j with _ | _ | j
    · simp [ν0]
    · simp [ν2]
    · rw [hQ0c _ (by omega)]; simp [coeff_C, coeff_X]
  have hQ1f : Q1 = C ν1 := by
    ext j
    rcases j with _ | j
    · simp [ν1]
    · rw [hQ1c _ (by omega)]; simp [coeff_C]
  have hcond : ∀ c, d c % 2 = 1 → ν0 + ν2 * a c + ξ c * ν1 = 0 := by
    intro c hc
    have := hval c hc
    rw [hQ0f, hQ1f] at this
    simpa [eval_add, eval_mul] using this
  have hν2 : Fm ≤ 2 → ν2 = 0 := fun h => hQ0c 1 (by omega)
  have hν1 : Fm ≤ 1 → ν1 = 0 := fun h => hQ1c 0 (by omega)
  have hν0 : Fm = 0 → ν0 = 0 := fun h => hQ0c 0 (by omega)
  -- the case analysis on the parities
  have hzero : ν0 = 0 ∧ ν1 = 0 ∧ ν2 = 0 := by
    have hFm' : Fm = d 0 % 2 + d 1 % 2 + d 2 % 2 := by rw [hFm, Fin.sum_univ_three]
    rcases Nat.mod_two_eq_zero_or_one (d 0) with h0 | h0 <;>
    rcases Nat.mod_two_eq_zero_or_one (d 1) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (d 2) with h2 | h2
    · exact ⟨hν0 (by omega), hν1 (by omega), hν2 (by omega)⟩
    · have := hcond 2 h2; rw [hν1 (by omega), hν2 (by omega)] at this
      exact ⟨by simpa using this, hν1 (by omega), hν2 (by omega)⟩
    · have := hcond 1 h1; rw [hν1 (by omega), hν2 (by omega)] at this
      exact ⟨by simpa using this, hν1 (by omega), hν2 (by omega)⟩
    · have e1 := hcond 1 h1; have e2 := hcond 2 h2
      rw [hν2 (by omega)] at e1 e2; simp only [zero_mul, add_zero] at e1 e2
      obtain ⟨a0, a1⟩ := solve2 (hξ.ne (by decide : (1 : Fin 3) ≠ 2)) e1 e2
      exact ⟨a0, a1, hν2 (by omega)⟩
    · have := hcond 0 h0; rw [hν1 (by omega), hν2 (by omega)] at this
      exact ⟨by simpa using this, hν1 (by omega), hν2 (by omega)⟩
    · have e1 := hcond 0 h0; have e2 := hcond 2 h2
      rw [hν2 (by omega)] at e1 e2; simp only [zero_mul, add_zero] at e1 e2
      obtain ⟨a0, a1⟩ := solve2 (hξ.ne (by decide : (0 : Fin 3) ≠ 2)) e1 e2
      exact ⟨a0, a1, hν2 (by omega)⟩
    · have e1 := hcond 0 h0; have e2 := hcond 1 h1
      rw [hν2 (by omega)] at e1 e2; simp only [zero_mul, add_zero] at e1 e2
      obtain ⟨a0, a1⟩ := solve2 (hξ.ne (by decide : (0 : Fin 3) ≠ 1)) e1 e2
      exact ⟨a0, a1, hν2 (by omega)⟩
    · refine solve3 a ξ hdet fun c => ?_
      fin_cases c
      · exact hcond 0 h0
      · exact hcond 1 h1
      · exact hcond 2 h2
  obtain ⟨z0, z1, z2⟩ := hzero
  have hQ0z : Q0 = 0 := by rw [hQ0f, z0, z2]; simp
  have hQ1z : Q1 = 0 := by rw [hQ1f, z1]; simp
  exact eq_zero_of_dualP V (by rw [hQ0, hQ0z, mul_zero]) (by rw [hQ1, hQ1z, mul_zero])

lemma dual_digit0_3 {s : ℕ} (a ξ : Fin s → F) (V : Fin 3 → F) (x : Fin s) :
    vecDigit (dualGen a ξ) V x 0 = V 0 + ξ x * V 1 + a x * V 2 := by
  simp [vecDigit, dualGen, pas, Fin.sum_univ_three]

lemma dual_digit1_3 {s : ℕ} (a ξ : Fin s → F) (V : Fin 3 → F) (x : Fin s) :
    vecDigit (dualGen a ξ) V x 1 = V 1 := by
  simp [vecDigit, dualGen, pas, Fin.sum_univ_three]

lemma dual_digit0_2 {s : ℕ} (a ξ : Fin s → F) (V : Fin 2 → F) (x : Fin s) :
    vecDigit (dualGen a ξ) V x 0 = V 0 + ξ x * V 1 := by
  simp [vecDigit, dualGen, pas, Fin.sum_univ_two]

lemma det_dual (a ξ : Fin 3 → F) :
    Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] =
      (a 1 - a 0) * (ξ 2 - ξ 0) - (a 2 - a 0) * (ξ 1 - ξ 0) := by
  rw [Matrix.det_fin_three]; simp; ring

section Fin

variable [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-- **`thm:dual`(a), failures**: if the places are not distinct, or the parameters are not distinct, or
the points `(a_c, ξ_c)` are collinear, then already the prefix `P_2` or `P_3` is not a net. -/
theorem dual_fail (D : DigitCode F q) (a ξ : Fin 3 → F)
    (h : ¬ (Function.Injective a ∧ Function.Injective ξ ∧
      Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] ≠ 0)) :
    ¬ BlockNet0 D (dualGen a ξ) 2 0 ∨ ¬ BlockNet0 D (dualGen a ξ) 3 0 := by
  by_cases ha : Function.Injective a
  · by_cases hξ : Function.Injective ξ
    · have hdet : Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] = 0 := by
        by_contra hd; exact h ⟨ha, hξ, hd⟩
      right
      intro hnet
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      have hV := kernel_of_blockNet0 D (dualGen a ξ) 3 hnet (fun _ => 1) (by simp)
        ![v 0, v 2, v 1] (fun x n hn => by
          have hn0 : n = 0 := by omega
          subst hn0
          rw [dual_digit0_3]
          have := congrFun hv x
          fin_cases x <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this ⊢ <;>
            linear_combination this)
      apply hv0
      funext i
      fin_cases i
      · exact congrFun hV 0
      · exact congrFun hV 2
      · exact congrFun hV 1
    · left
      intro hnet
      obtain ⟨c, c', hcc, hne⟩ := Function.not_injective_iff.1 hξ
      have hV := kernel_of_blockNet0 D (dualGen a ξ) 2 hnet
        (fun x => (if x = c then 1 else 0) + (if x = c' then 1 else 0))
        (by simp [Finset.sum_add_distrib]) ![-ξ c, 1] (fun x n hn => by
          have hn0 : n = 0 := by split_ifs at hn <;> omega
          subst hn0
          rw [dual_digit0_2]
          have hx : x = c ∨ x = c' := by
            by_contra hx; push_neg at hx; simp [hx.1, hx.2] at hn
          rcases hx with rfl | rfl
          · simp
          · simp [hcc])
      have := congrFun hV 1
      simp at this
  · right
    intro hnet
    obtain ⟨c, c', hcc, hne⟩ := Function.not_injective_iff.1 ha
    have hV := kernel_of_blockNet0 D (dualGen a ξ) 3 hnet
      (fun x => (if x = c then 1 else 0) + (if x = c' then 2 else 0))
      (by simp [Finset.sum_add_distrib]) ![-a c, 0, 1] (fun x n hn => by
        have hx : x = c ∨ x = c' := by
          by_contra hx; push_neg at hx; simp [hx.1, hx.2] at hn
        rcases Nat.lt_or_ge n 1 with h1 | h1
        · have hn0 : n = 0 := by omega
          subst hn0
          rw [dual_digit0_3]
          rcases hx with rfl | rfl
          · simp
          · simp [hcc]
        · have hn1 : n = 1 := by
            rcases hx with rfl | rfl
            · simp [hne] at hn; omega
            · simp [Ne.symm hne] at hn; omega
          subst hn1
          rw [dual_digit1_3]; simp)
    have := congrFun hV 2
    simp at this

/-- **`thm:dual`(a)**: the dual-number Faure matrices `eq:dual` (`s = 3`, any finite field) form a
digital `(0,3)`-sequence iff the places `a_c` are distinct, the parameters `ξ_c` are distinct, and the
points `(a_c, ξ_c)` are not collinear (`det(1, a_c, ξ_c) ≠ 0`). Every failure occurs at `m ≤ 3`
(`dual_fail`). -/
theorem dual_a (D : DigitCode F q) (a ξ : Fin 3 → F) :
    IsSeq0 D (dualGen a ξ) ↔ Function.Injective a ∧ Function.Injective ξ ∧
      Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] ≠ 0 := by
  constructor
  · intro hseq
    by_contra h
    rcases dual_fail D a ξ h with h2 | h3
    · exact h2 (hseq 2 0)
    · exact h3 (hseq 3 0)
  · rintro ⟨ha, hξ, hdet⟩
    rw [det_dual] at hdet
    exact isSeq0_of_kernel D _ fun m d hd V hV => dual_kernel a ξ ha hξ hdet m d hd V hV

end Fin

end GeoSeq
