/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs
public import GeoSeq.V1Aux
public import GeoSeq.Window

@[expose] public section

/-!
# GeoSeq stage V5: the bound for staggered windows at a finite prime (`lem:W`)

* `sumset_lift`: elements of a sumset of integer windows have integer representatives.
* **`lemW`** (`lem:W`): under (D) and (N), `LB(W) ≥ LB_W` with `LB_W² = min(T⋆, T_{C⋆}, T_2)`, every `s ≥ 2`, every
  staggered coordinate; `M` is any upper bound of the `M_i` (the paper's `M = max_i M_i`).
* **`lemW_last`** (the last statement of `lem:W`): under its three inequalities `LB_W = 1 - M⋆/p`;
  **`lemW_lb`**: both together, `LB(W) ≥ 1 - M⋆/p`.
-/

namespace GeoSeq

open Finset

section Lift

variable {s : ℕ}

/-- Elements of a sumset of integer windows have integer representatives. -/
lemma sumset_lift {p : ℕ} (W : Fin s → Fin s → Set (ZMod p)) (lo hi : Fin s → Fin s → ℤ)
    (hW : ∀ c c', W c c' = intWin p (lo c c') (hi c c')) (e : Fin s → ℤ) (c : Fin s) (σ : ZMod p)
    (hσ : σ ∈ sumsetS W e c) :
    ∃ z : Fin s → ℤ, (∀ c', e c' ≠ 0 → lo c c' ≤ z c' ∧ z c' ≤ hi c c') ∧ (∀ c', e c' = 0 → z c' = 0) ∧
      σ = ((∑ c', e c' * z c' : ℤ) : ZMod p) := by
  classical
  obtain ⟨x, hx, rfl⟩ := hσ
  have h : ∀ c', ∃ z : ℤ, (e c' ≠ 0 → lo c c' ≤ z ∧ z ≤ hi c c' ∧ (z : ZMod p) = x c') ∧ (e c' = 0 → z = 0) := by
    intro c'
    by_cases h0 : e c' = 0
    · exact ⟨0, fun h => absurd h0 h, fun _ => rfl⟩
    · have := hx c' h0
      rw [hW] at this
      obtain ⟨z, h1, h2, h3⟩ := this
      exact ⟨z, fun _ => ⟨h1, h2, h3⟩, fun h => absurd h h0⟩
  choose z hz1 hz2 using h
  refine ⟨z, fun c' h => ⟨(hz1 c' h).1, (hz1 c' h).2.1⟩, hz2, ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun c' _ => ?_
  by_cases h0 : e c' = 0
  · simp [h0]
  · rw [(hz1 c' h0).2.2]

end Lift

section W

variable {s : ℕ}

/-- The lower ends of the staggered windows. -/
def stagLo (p : ℕ) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ) (c c' : Fin s) : ℤ :=
  if c' = cs then (if c = cs then -((Mv cs : ℤ) - 1) else -(Bcs : ℤ))
  else if c = c' then -((A : ℤ) + Mv c' - 1)
  else if c = cs then halfZ p - Bsc
  else -(Bcc : ℤ)

/-- The upper ends of the staggered windows. -/
def stagHi (p : ℕ) (cs : Fin s) (A : ℕ) (Bcc Bsc Bcs : ℕ) (c c' : Fin s) : ℤ :=
  if c' = cs then (if c = cs then 0 else (Bcs : ℤ))
  else if c = c' then -(A : ℤ)
  else if c = cs then halfZ p + Bsc
  else (Bcc : ℤ)

lemma stagWin_eq (p : ℕ) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ) (c c' : Fin s) :
    stagWin p cs A Mv Bcc Bsc Bcs c c' =
      intWin p (stagLo p cs A Mv Bcc Bsc Bcs c c') (stagHi p cs A Bcc Bsc Bcs c c') := by
  unfold stagWin stagLo stagHi
  split_ifs <;> rfl

lemma sign_of' (e : ℤ) (h1 : -1 ≤ e) (h2 : e ≤ 1) (h : e ≠ 0) : e = 1 ∨ e = -1 := by omega

/-- `gapNum1 p e σ = gapNum1 p 1 (e σ)` for `e = ±1`. -/
lemma gap_sign (p : ℕ) [NeZero p] (e : ℤ) (he : e = 1 ∨ e = -1) (σ : ZMod p) :
    gapNum1 p e σ = gapNum1 p 1 ((e : ZMod p) * σ) := by
  rcases he with rfl | rfl
  · simp
  · rw [F1_neg]; simp

/-- The cross half-widths into a row `i ∈ C`: `B_{i←c⋆} = B_{C←⋆}`, `B_{i←j} = B_{C←C}`. -/
def rowB (cs : Fin s) (Bcc Bcs : ℕ) (c' : Fin s) : ℤ := if c' = cs then (Bcs : ℤ) else Bcc

lemma rowR_le (cs i : Fin s) (hi : i ≠ cs) (Bcc Bcs : ℕ) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) :
    ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c' ≤ ((s - 2 : ℕ) : ℤ) * Bcc + Bcs := by
  have hcs : cs ∈ univ.erase i := mem_erase.mpr ⟨Ne.symm hi, mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hcs]
  have h1 : |e cs| * rowB cs Bcc Bcs cs ≤ Bcs := by
    simp only [rowB, if_true]
    have : |e cs| ≤ 1 := abs_le.mpr ⟨(he cs).1, (he cs).2⟩
    nlinarith [abs_nonneg (e cs)]
  have h2 : ∑ c' ∈ (univ.erase i).erase cs, |e c'| * rowB cs Bcc Bcs c' ≤
      ∑ c' ∈ (univ.erase i).erase cs, (Bcc : ℤ) := by
    refine Finset.sum_le_sum fun c' hc' => ?_
    have hne : c' ≠ cs := Finset.ne_of_mem_erase hc'
    simp only [rowB, if_neg hne]
    have : |e c'| ≤ 1 := abs_le.mpr ⟨(he c').1, (he c').2⟩
    nlinarith [abs_nonneg (e c')]
  rw [Finset.sum_const, Finset.card_erase_of_mem hcs, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  have : ((s - 1 - 1 : ℕ) : ℤ) = ((s - 2 : ℕ) : ℤ) := by congr 1
  rw [this] at h2
  linarith

variable {p : ℕ} [Fact p.Prime]

/-- A moving coordinate `i ∈ C` (proof of `lem:W`): `p f_1(e_i, σ_i) ≥ p - A - M_i - R_i`,
`R_i = ∑_{c' ≠ i} |e_{c'}| B_{i←c'}`, given `R_i ≤ A` and `A + M_i + R_i ≤ p`. -/
lemma lemW_rowC (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (i : Fin s) (hi : i ≠ cs) (hei : e i ≠ 0)
    (σ : ZMod p) (hσ : σ ∈ sumsetS (stagWin p cs A Mv Bcc Bsc Bcs) e i)
    (hRA : ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c' ≤ A)
    (hRp : (A : ℤ) + Mv i + ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c' ≤ p) :
    (p : ℤ) - A - Mv i - ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c' ≤ gapNum1 p (e i) σ := by
  obtain ⟨z, hz, hz0, rfl⟩ := sumset_lift _ _ _ (stagWin_eq p cs A Mv Bcc Bsc Bcs) e i σ hσ
  have hs1 := sign_of' (e i) (he i).1 (he i).2 hei
  rw [gap_sign p (e i) hs1]
  have hei2 : e i * e i = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  have hzi := hz i hei
  simp only [stagLo, stagHi, if_neg hi, if_true] at hzi
  set R := ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c'
  have hsplit : e i * ∑ c', e c' * z c' = z i + ∑ c' ∈ univ.erase i, e i * (e c' * z c') := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), mul_add, Finset.mul_sum, ← mul_assoc, hei2, one_mul]
  have hrest : |∑ c' ∈ univ.erase i, e i * (e c' * z c')| ≤ R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c' hc' => ?_)
    have hic : c' ≠ i := Finset.ne_of_mem_erase hc'
    have hei1 : |e i| = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
    rw [abs_mul, abs_mul, hei1, one_mul]
    by_cases h0 : e c' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := hz c' h0
      by_cases hcs : c' = cs
      · subst hcs; simp only [stagLo, stagHi, rowB, if_true, if_neg hi] at this ⊢
        exact abs_le.mpr this
      · simp only [stagLo, stagHi, rowB, if_neg hcs, if_neg (Ne.symm hic), if_neg hi] at this ⊢
        exact abs_le.mpr this
  have hcast : ((e i : ℤ) : ZMod p) * ((∑ c', e c' * z c' : ℤ) : ZMod p) =
      ((z i + ∑ c' ∈ univ.erase i, e i * (e c' * z c') : ℤ) : ZMod p) := by
    rw [← hsplit]; push_cast; ring
  rw [hcast]
  set Z := ∑ c' ∈ univ.erase i, e i * (e c' * z c')
  have hZ := abs_le.mp hrest
  rw [f1_int_nonpos p _ (by omega) (by omega)]
  omega

/-- Row `c⋆` of the step `E = {c⋆}`: `p f_1(e_⋆, σ_⋆) ≥ p - M⋆`. -/
lemma lemW_rowS (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ) (hMp : Mv cs ≤ p)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hcs : e cs ≠ 0) (hoth : ∀ c, c ≠ cs → e c = 0)
    (σ : ZMod p) (hσ : σ ∈ sumsetS (stagWin p cs A Mv Bcc Bsc Bcs) e cs) :
    (p : ℤ) - Mv cs ≤ gapNum1 p (e cs) σ := by
  obtain ⟨z, hz, hz0, rfl⟩ := sumset_lift _ _ _ (stagWin_eq p cs A Mv Bcc Bsc Bcs) e cs σ hσ
  have hs1 := sign_of' (e cs) (he cs).1 (he cs).2 hcs
  rw [gap_sign p (e cs) hs1]
  have hzc := hz cs hcs
  simp only [stagLo, stagHi, if_true] at hzc
  have hsum : ∑ c', e c' * z c' = e cs * z cs :=
    Finset.sum_eq_single cs (fun c _ hc => by rw [hoth c hc]; simp) (by simp)
  have hcast : ((e cs : ℤ) : ZMod p) * ((∑ c', e c' * z c' : ℤ) : ZMod p) = ((z cs : ℤ) : ZMod p) := by
    rw [hsum]; push_cast
    rcases hs1 with h | h <;> rw [h] <;> push_cast <;> ring
  rw [hcast, f1_int_nonpos p _ (by omega) (by omega)]
  omega

lemma halfZ_two (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : 2 * halfZ p = p + 1 := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  unfold halfZ; omega

/-- Row `c⋆` of the step `E = {i}` (`i ∈ C`, `c⋆` does not move): `2p f_1(0, σ_⋆) ≥ p - 3 - 2B_{⋆←C}`. -/
lemma lemW_rowS0 (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ) (hp : 5 ≤ p)
    (hB : 2 * Bsc + 3 ≤ p)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (i : Fin s) (hi : i ≠ cs) (hei : e i ≠ 0)
    (hcs : e cs = 0) (hoth : ∀ c, c ≠ cs → c ≠ i → e c = 0)
    (σ : ZMod p) (hσ : σ ∈ sumsetS (stagWin p cs A Mv Bcc Bsc Bcs) e cs) :
    (p : ℤ) - 3 - 2 * Bsc ≤ 2 * (gapNum1 p (e cs) σ : ℤ) := by
  obtain ⟨z, hz, hz0, rfl⟩ := sumset_lift _ _ _ (stagWin_eq p cs A Mv Bcc Bsc Bcs) e cs σ hσ
  have hs1 := sign_of' (e i) (he i).1 (he i).2 hei
  have hzi := hz i hei
  simp only [stagLo, stagHi, if_neg hi, if_neg (Ne.symm hi), if_true] at hzi
  have hsum : ∑ c', e c' * z c' = e i * z i :=
    Finset.sum_eq_single i (fun c _ hc => by
      by_cases hc' : c = cs
      · rw [hc', hcs]; simp
      · rw [hoth c hc' hc]; simp) (by simp)
  have h2 := halfZ_two p (by omega)
  rw [hcs, hsum]
  have hval : ∀ w : ℤ, 0 ≤ w → w < p → (p : ℤ) - 3 - 2 * Bsc ≤ 2 * (gapNum1 p 0 (w : ZMod p) : ℤ) →
      (p : ℤ) - 3 - 2 * Bsc ≤ 2 * (gapNum1 p 0 ((-w : ℤ) : ZMod p) : ℤ) := by
    intro w _ _ h
    push_cast; rwa [F0_neg]
  have hpos : (p : ℤ) - 3 - 2 * Bsc ≤ 2 * (gapNum1 p 0 ((z i : ℤ) : ZMod p) : ℤ) := by
    rw [f0_int p _ (by omega) (by omega)]
    have h3 : (p - 3 - 2 * Bsc : ℤ) ≤ 2 * (((min (z i).toNat (p - (z i).toNat)) - 1 : ℕ) : ℤ) := by
      have ht : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (by omega)
      have hnp : (z i).toNat ≤ p := by omega
      have hge : (p : ℤ) - 1 - 2 * Bsc ≤ 2 * ((min (z i).toNat (p - (z i).toNat) : ℕ) : ℤ) := by
        rcases Nat.le_total (z i).toNat (p - (z i).toNat) with hle | hle
        · rw [min_eq_left hle, ht]; omega
        · rw [min_eq_right hle, Nat.cast_sub hnp, ht]; omega
      omega
    exact_mod_cast h3
  rcases hs1 with h | h
  · rw [h]; simpa using hpos
  · rw [h]
    have := hval (z i) (by omega) (by omega) hpos
    simpa using this

/-- Row `c⋆` of the step `E = {i, c⋆}`: `2p f_1(e_⋆, σ_⋆) ≥ p - 1 - 2B_{⋆←C} - 2M⋆`. -/
lemma lemW_rowS1 (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (Bcc Bsc Bcs : ℕ) (hp : 5 ≤ p)
    (hB : 2 * Bsc + 2 * Mv cs + 3 ≤ p) (hM1 : 1 ≤ Mv cs)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (i : Fin s) (hi : i ≠ cs) (hei : e i ≠ 0)
    (hcs : e cs ≠ 0) (hoth : ∀ c, c ≠ cs → c ≠ i → e c = 0)
    (σ : ZMod p) (hσ : σ ∈ sumsetS (stagWin p cs A Mv Bcc Bsc Bcs) e cs) :
    (p : ℤ) - 1 - 2 * Bsc - 2 * Mv cs ≤ 2 * (gapNum1 p (e cs) σ : ℤ) := by
  obtain ⟨z, hz, hz0, rfl⟩ := sumset_lift _ _ _ (stagWin_eq p cs A Mv Bcc Bsc Bcs) e cs σ hσ
  have hsi := sign_of' (e i) (he i).1 (he i).2 hei
  have hsc := sign_of' (e cs) (he cs).1 (he cs).2 hcs
  have hzi := hz i hei
  simp only [stagLo, stagHi, if_neg hi, if_neg (Ne.symm hi), if_true] at hzi
  have hzc := hz cs hcs
  simp only [stagLo, stagHi, if_true] at hzc
  have hsum : ∑ c', e c' * z c' = e cs * z cs + e i * z i := by
    have hsub : ∑ c', e c' * z c' = ∑ c' ∈ ({cs, i} : Finset (Fin s)), e c' * z c' := by
      refine (Finset.sum_subset (subset_univ _) fun c _ hc => ?_).symm
      simp only [mem_insert, mem_singleton, not_or] at hc
      rw [hoth c hc.1 hc.2]; simp
    rw [hsub, Finset.sum_pair (Ne.symm hi)]
  have h2 := halfZ_two p (by omega)
  rw [gap_sign p (e cs) hsc, hsum]
  have hcs2 : e cs * e cs = 1 := by rcases hsc with h | h <;> rw [h] <;> norm_num
  have hcast : ((e cs : ℤ) : ZMod p) * ((e cs * z cs + e i * z i : ℤ) : ZMod p) =
      ((z cs + e cs * e i * z i : ℤ) : ZMod p) := by
    have : e cs * (e cs * z cs + e i * z i) = z cs + e cs * e i * z i := by
      rw [mul_add, ← mul_assoc, hcs2, one_mul, mul_assoc]
    rw [← this]; push_cast; ring
  rw [hcast]
  have hprod : e cs * e i = 1 ∨ e cs * e i = -1 := by
    rcases hsi with h | h <;> rcases hsc with h' | h' <;> rw [h, h'] <;> norm_num
  rcases hprod with h | h
  · rw [h, one_mul, f1_int_pos p _ (by omega) (by omega)]
    omega
  · rw [h]
    have he' : ((z cs + -1 * z i : ℤ) : ZMod p) = ((z cs + -1 * z i + p : ℤ) : ZMod p) := by
      push_cast; simp
    rw [he', f1_int_pos p _ (by omega) (by omega)]
    omega

lemma real_sq_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha h 2

lemma sum_ge_two' (f : Fin s → ℝ) (hf : ∀ c, 0 ≤ f c) {i j : Fin s} (hij : i ≠ j) :
    f i + f j ≤ ∑ c, f c := by
  rw [← Finset.sum_pair hij]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ => hf c

/-- **`lem:W`** (bound for staggered windows): let `s ≥ 2`, `p` an odd prime, integers `A ≥ 0`, `M_i ≥ 1`,
`M⋆ ≥ 1` and `M ≥ max_{i ∈ C} M_i`, with (D) `A ≥ (s-2)B_{C←C} + B_{C←⋆}` and (N)
`A + M + (s-2)B_{C←C} + B_{C←⋆} ≤ p`, `2B_{⋆←C} + 2M⋆ ≤ p - 3`. Then the staggered windows have
`LB(W) ≥ LB_W`, `LB_W² = min(T⋆, T_{C⋆}, T_2)` (`T_2` omitted for `s = 2`). -/
theorem lemW (hs : 2 ≤ s) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (M Bcc Bsc Bcs : ℕ)
    (hM1 : ∀ c, 1 ≤ Mv c) (hM : ∀ i, i ≠ cs → Mv i ≤ M)
    (hD : (s - 2) * Bcc + Bcs ≤ A) (hN1 : A + M + (s - 2) * Bcc + Bcs ≤ p)
    (hN2 : 2 * Bsc + 2 * Mv cs ≤ p - 3) :
    WinLB p (stagWin p cs A Mv Bcc Bsc Bcs) (lbW p s A M (Mv cs) Bcc Bsc Bcs) := by
  intro e he hne σ hσ
  have hMc := hM1 cs
  have hp5 : 5 ≤ p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hnn : ∀ c, 0 ≤ ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2 := fun c => sq_nonneg _
  -- the bound `m ≤ ∑` suffices
  suffices hm : (if 3 ≤ s then min (min (wTst p (Mv cs)) (wTCs p A M (Mv cs) Bsc Bcs)) (wT2 p s A M Bcc Bcs)
      else min (wTst p (Mv cs)) (wTCs p A M (Mv cs) Bsc Bcs)) ≤ ∑ c, ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2 by
    exact Real.sqrt_le_sqrt hm
  have hmin_st : (if 3 ≤ s then min (min (wTst p (Mv cs)) (wTCs p A M (Mv cs) Bsc Bcs)) (wT2 p s A M Bcc Bcs)
      else min (wTst p (Mv cs)) (wTCs p A M (Mv cs) Bsc Bcs)) ≤ wTst p (Mv cs) := by
    split_ifs
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  have hmin_cs : (if 3 ≤ s then min (min (wTst p (Mv cs)) (wTCs p A M (Mv cs) Bsc Bcs)) (wT2 p s A M Bcc Bcs)
      else min (wTst p (Mv cs)) (wTCs p A M (Mv cs) Bsc Bcs)) ≤ wTCs p A M (Mv cs) Bsc Bcs := by
    split_ifs
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact min_le_right _ _
  -- the general bound for a moving coordinate of `C`
  have hrowC : ∀ i, i ≠ cs → e i ≠ 0 →
      (p : ℤ) - A - Mv i - ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c' ≤ gapNum1 p (e i) (σ i) := by
    intro i hi hei
    have hR := rowR_le cs i hi Bcc Bcs e he
    have hMi := hM i hi
    have hsub : ((s - 2 : ℕ) : ℤ) = ((s - 2) : ℕ) := rfl
    refine lemW_rowC cs A Mv Bcc Bsc Bcs e he i hi hei (σ i) (hσ i) ?_ ?_
    · have : ((s - 2 : ℕ) : ℤ) * Bcc + Bcs ≤ A := by exact_mod_cast hD
      linarith
    · have : (A : ℤ) + M + ((s - 2 : ℕ) : ℤ) * Bcc + Bcs ≤ p := by exact_mod_cast hN1
      have : (Mv i : ℤ) ≤ M := by exact_mod_cast hMi
      linarith
  by_cases hA : ∃ i j, i ≠ cs ∧ j ≠ cs ∧ e i ≠ 0 ∧ e j ≠ 0 ∧ i ≠ j
  · -- `k ≥ 2`: two moving coordinates of `C` give `T_2`
    obtain ⟨i, j, hi, hj, hei, hej, hij⟩ := hA
    have hs3 : 3 ≤ s := by
      by_contra h
      have : s = 2 := by omega
      subst this
      have : ∀ c : Fin 2, c ≠ cs → c = 1 - cs := by
        intro c hc; fin_cases c <;> fin_cases cs <;> simp_all
      exact hij ((this i hi).trans (this j hj).symm)
    have hbound : ∀ i, i ≠ cs → e i ≠ 0 →
        (p : ℝ) - A - M - ((s - 2 : ℕ) : ℝ) * Bcc - Bcs ≤ gapNum1 p (e i) (σ i) := by
      intro i hi hei
      have h1 := hrowC i hi hei
      have hR := rowR_le cs i hi Bcc Bcs e he
      have hMi : (Mv i : ℤ) ≤ M := by exact_mod_cast hM i hi
      have : (p : ℤ) - A - M - ((s - 2 : ℕ) : ℤ) * Bcc - Bcs ≤ gapNum1 p (e i) (σ i) := by linarith
      exact_mod_cast this
    have hb0 : 0 ≤ 1 - ((A : ℝ) + M + ((s - 2 : ℕ) : ℝ) * Bcc + Bcs) / p := by
      rw [sub_nonneg, div_le_one hpR]; exact_mod_cast hN1
    have hfi : 1 - ((A : ℝ) + M + ((s - 2 : ℕ) : ℝ) * Bcc + Bcs) / p ≤ (gapNum1 p (e i) (σ i) : ℝ) / p := by
      rw [one_sub_div hpR.ne', div_le_div_iff_of_pos_right hpR]; linarith [hbound i hi hei]
    have hfj : 1 - ((A : ℝ) + M + ((s - 2 : ℕ) : ℝ) * Bcc + Bcs) / p ≤ (gapNum1 p (e j) (σ j) : ℝ) / p := by
      rw [one_sub_div hpR.ne', div_le_div_iff_of_pos_right hpR]; linarith [hbound j hj hej]
    have h2 := sum_ge_two' (fun c => ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2) hnn hij
    have hT2 : wT2 p s A M Bcc Bcs ≤ ∑ c, ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2 := by
      unfold wT2
      have := real_sq_le hb0 hfi
      have := real_sq_le hb0 hfj
      linarith
    rw [if_pos hs3]
    exact (min_le_right _ _).trans hT2
  · push_neg at hA
    by_cases hB : ∃ i, i ≠ cs ∧ e i ≠ 0
    · obtain ⟨i, hi, hei⟩ := hB
      have hoth : ∀ c, c ≠ cs → c ≠ i → e c = 0 := by
        intro c hc hci
        by_contra h
        exact hci (hA c i hc hi h hei)
      have hR : ∑ c' ∈ univ.erase i, |e c'| * rowB cs Bcc Bcs c' = |e cs| * Bcs := by
        rw [Finset.sum_eq_single_of_mem cs (mem_erase.mpr ⟨Ne.symm hi, mem_univ _⟩)]
        · simp [rowB]
        · intro c hc hccs
          rw [hoth c hccs (Finset.ne_of_mem_erase hc)]; simp
      have h1 := hrowC i hi hei
      rw [hR] at h1
      have hMi : (Mv i : ℤ) ≤ M := by exact_mod_cast hM i hi
      have hecs1 : |e cs| ≤ 1 := abs_le.mpr ⟨(he cs).1, (he cs).2⟩
      have hgi : (p : ℝ) - A - M - Bcs ≤ gapNum1 p (e i) (σ i) := by
        have : (p : ℤ) - A - M - Bcs ≤ gapNum1 p (e i) (σ i) := by nlinarith [abs_nonneg (e cs)]
        exact_mod_cast this
      have hb0 : 0 ≤ 1 - ((A : ℝ) + M + Bcs) / p := by
        rw [sub_nonneg, div_le_one hpR]
        have : A + M + Bcs ≤ p := by have := Nat.zero_le ((s - 2) * Bcc); omega
        exact_mod_cast this
      have hfi : 1 - ((A : ℝ) + M + Bcs) / p ≤ (gapNum1 p (e i) (σ i) : ℝ) / p := by
        rw [one_sub_div hpR.ne', div_le_div_iff_of_pos_right hpR]; linarith
      have hgcs : (p : ℝ) - 1 - 2 * Bsc - 2 * Mv cs ≤ 2 * (gapNum1 p (e cs) (σ cs) : ℝ) := by
        by_cases hcs : e cs = 0
        · have := lemW_rowS0 cs A Mv Bcc Bsc Bcs hp5 (by omega) e he i hi hei hcs hoth (σ cs) (hσ cs)
          have : (p : ℤ) - 1 - 2 * Bsc - 2 * Mv cs ≤ 2 * (gapNum1 p (e cs) (σ cs) : ℤ) := by omega
          exact_mod_cast this
        · have := lemW_rowS1 cs A Mv Bcc Bsc Bcs hp5 (by omega) hMc e he i hi hei hcs hoth (σ cs) (hσ cs)
          exact_mod_cast this
      have hc0 : 0 ≤ ((p : ℝ) - 1 - 2 * Bsc - 2 * Mv cs) / (2 * p) := by
        apply div_nonneg _ (by positivity)
        have : 2 * Bsc + 2 * Mv cs + 1 ≤ p := by omega
        have : (2 * Bsc + 2 * Mv cs + 1 : ℝ) ≤ p := by exact_mod_cast this
        linarith
      have hfc : ((p : ℝ) - 1 - 2 * Bsc - 2 * Mv cs) / (2 * p) ≤ (gapNum1 p (e cs) (σ cs) : ℝ) / p := by
        rw [div_le_div_iff₀ (by positivity) hpR]; nlinarith
      have h2 := sum_ge_two' (fun c => ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2) hnn hi
      refine hmin_cs.trans ?_
      unfold wTCs
      have := real_sq_le hb0 hfi
      have := real_sq_le hc0 hfc
      linarith
    · -- `E = {c⋆}`
      push_neg at hB
      have hcs : e cs ≠ 0 := by
        obtain ⟨c, hc⟩ := hne
        by_contra h
        by_cases hcc : c = cs
        · exact hc (hcc ▸ h)
        · exact hc (hB c hcc)
      have h1 := lemW_rowS cs A Mv Bcc Bsc Bcs (by omega) e he hcs hB (σ cs) (hσ cs)
      have hb0 : 0 ≤ 1 - (Mv cs : ℝ) / p := by
        rw [sub_nonneg, div_le_one hpR]; exact_mod_cast (show Mv cs ≤ p by omega)
      have hf : 1 - (Mv cs : ℝ) / p ≤ (gapNum1 p (e cs) (σ cs) : ℝ) / p := by
        rw [one_sub_div hpR.ne', div_le_div_iff_of_pos_right hpR]
        have : (p : ℝ) - Mv cs ≤ gapNum1 p (e cs) (σ cs) := by exact_mod_cast h1
        linarith
      have := Finset.single_le_sum (fun c _ => hnn c) (mem_univ cs)
      refine hmin_st.trans ?_
      unfold wTst
      have := real_sq_le hb0 hf
      linarith

/-- **`lem:W`, last statement**: with `x = 1 - ((s-2)B_{C←C} + 2B_{C←⋆})/p`, `y = ½ - B_{⋆←C}/p` and
`A = (s-2)B_{C←C} + B_{C←⋆}`: if `x ≥ M/p`, `p(x² + y² - 1) ≥ 2xM + 2y(M⋆ + ½)` and `1 - (2A+M)/p ≥ 1/√2`, then
`LB_W = 1 - M⋆/p` (here only `M⋆ ≤ p` of the lemma's hypotheses is used). -/
theorem lemW_last (p s A M Mst Bcc Bsc Bcs : ℕ) (hp : 0 < p) (hMst : Mst ≤ p)
    (hA : A = (s - 2) * Bcc + Bcs)
    (hx : (M : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p)
    (hxy : 2 * (1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) * M + 2 * (1 / 2 - (Bsc : ℝ) / p) * (Mst + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) ^ 2 + (1 / 2 - (Bsc : ℝ) / p) ^ 2 - 1))
    (hz : 1 / Real.sqrt 2 ≤ 1 - (2 * (A : ℝ) + M) / p) :
    lbW p s A M Mst Bcc Bsc Bcs = 1 - (Mst : ℝ) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hst0 : 0 ≤ 1 - (Mst : ℝ) / p := by
    rw [sub_nonneg, div_le_one hpR]; exact_mod_cast hMst
  have hst1 : 1 - (Mst : ℝ) / p ≤ 1 := by
    have : 0 ≤ (Mst : ℝ) / p := by positivity
    linarith
  have hAR : (A : ℝ) = ((s - 2 : ℕ) : ℝ) * Bcc + Bcs := by rw [hA]; push_cast; ring
  set x := 1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p with hxdef
  set y := 1 / 2 - (Bsc : ℝ) / p with hydef
  -- `T_{C⋆} ≥ 1`
  have hTC : 1 ≤ wTCs p A M Mst Bsc Bcs := by
    unfold wTCs
    have e1 : 1 - ((A : ℝ) + M + Bcs) / p = x - M / p := by
      rw [hxdef, hAR]; field_simp; ring
    have e2 : ((p : ℝ) - 1 - 2 * Bsc - 2 * Mst) / (2 * p) = y - (Mst + 1 / 2) / p := by
      rw [hydef]; field_simp; ring
    rw [e1, e2]
    have key : x ^ 2 + y ^ 2 - 2 * x * (M / p) - 2 * y * ((Mst + 1 / 2) / p) ≥ 1 := by
      have h' : (2 * x * M + 2 * y * (Mst + 1 / 2)) / p ≤ x ^ 2 + y ^ 2 - 1 := by
        rw [div_le_iff₀ hpR]; linarith
      have : 2 * x * (M / p) + 2 * y * ((Mst + 1 / 2) / p) = (2 * x * M + 2 * y * (Mst + 1 / 2)) / p := by
        field_simp
      linarith
    nlinarith [sq_nonneg (M / p : ℝ), sq_nonneg ((Mst + 1 / 2) / p : ℝ)]
  -- `T_2 ≥ 1`
  have hT2 : 1 ≤ wT2 p s A M Bcc Bcs := by
    unfold wT2
    have e3 : 1 - ((A : ℝ) + M + ((s - 2 : ℕ) : ℝ) * Bcc + Bcs) / p = 1 - (2 * (A : ℝ) + M) / p := by
      rw [hAR]; ring
    rw [e3]
    have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have h0 : 0 ≤ 1 / Real.sqrt 2 := by positivity
    have := real_sq_le h0 hz
    linarith
  have hTs : wTst p Mst ≤ 1 := by
    unfold wTst; nlinarith
  unfold lbW
  have hm : (if 3 ≤ s then min (min (wTst p Mst) (wTCs p A M Mst Bsc Bcs)) (wT2 p s A M Bcc Bcs)
      else min (wTst p Mst) (wTCs p A M Mst Bsc Bcs)) = wTst p Mst := by
    split_ifs
    · rw [min_eq_left (hTs.trans hTC), min_eq_left (hTs.trans hT2)]
    · rw [min_eq_left (hTs.trans hTC)]
  rw [hm, wTst, Real.sqrt_sq hst0]

/-- **`lem:W` with its last statement**: under (D), (N) and the three inequalities of the last statement,
the staggered windows have `LB(W) ≥ 1 - M⋆/p`. -/
theorem lemW_lb (hs : 2 ≤ s) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (M Bcc Bsc Bcs : ℕ)
    (hM1 : ∀ c, 1 ≤ Mv c) (hM : ∀ i, i ≠ cs → Mv i ≤ M)
    (hA : A = (s - 2) * Bcc + Bcs) (hN1 : A + M + (s - 2) * Bcc + Bcs ≤ p)
    (hN2 : 2 * Bsc + 2 * Mv cs ≤ p - 3)
    (hx : (M : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p)
    (hxy : 2 * (1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) * M + 2 * (1 / 2 - (Bsc : ℝ) / p) * (Mv cs + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) ^ 2 + (1 / 2 - (Bsc : ℝ) / p) ^ 2 - 1))
    (hz : 1 / Real.sqrt 2 ≤ 1 - (2 * (A : ℝ) + M) / p) :
    WinLB p (stagWin p cs A Mv Bcc Bsc Bcs) (1 - (Mv cs : ℝ) / p) := by
  have h := lemW hs cs A Mv M Bcc Bsc Bcs hM1 hM (le_of_eq hA.symm) hN1 hN2
  have hMc := hM1 cs
  rwa [lemW_last p s A M (Mv cs) Bcc Bsc Bcs (by omega) (by omega) hA hx hxy hz] at h

end W

end GeoSeq
