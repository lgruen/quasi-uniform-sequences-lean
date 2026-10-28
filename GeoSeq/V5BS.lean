/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs

@[expose] public section

/-!
# GeoSeq stage V5: the staggered windows in the continuum (`thm:BS`)

* **`BS`**: under `(s-1)ε < a ≤ 1-ε` and `(1-a-ε)² + (½-ε)² ≥ 1` (the paper's form, `thm:BS`; in Lean
  `a ≤ 1-ε` is the hypothesis `a + ε ≤ 1`), the staggered continuum windows have `c*(W) ≥ 1`. (The upper bound
  `a ≤ 1-ε` was added to the paper after this formalization: without a smallness condition the statement fails,
  e.g. `s = 2`, `ε = 0.95`, `a = 0.99`: windows of width `1.9` cover the circle. The paper's proof uses
  `1 - a - ε ≥ 0` when it takes the square root in (ii).)
* **`BS_exists`**: for every `0 < ε < ε_s` such an `a` exists (explicit `a = (s-1)ε + G(ε)/2`, no IVT);
  `epsS_root`, `epsS_least` (`ε_s` is the smaller root of `(1-sε)² + (½-ε)² = 1`), `epsS_three`
  (`ε_3 = (7-√39)/20`, `0.0377 < ε_3 < 0.0378`).
-/

namespace GeoSeq

open Finset

section Fbar

lemma fbar_one_of (Φ : ℝ) (h0 : -1 < Φ) (h1 : Φ < 0) : fbar 1 Φ = 1 + Φ := by
  have : Int.fract (-Φ) = -Φ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  simp only [fbar, if_true, this]; ring

lemma fbar_m1 (Φ : ℝ) : fbar (-1) Φ = fbar 1 (-Φ) := by simp [fbar]

lemma fbar_sign (e : ℤ) (he : e = 1 ∨ e = -1) (Φ : ℝ) (h0 : -1 < (e : ℝ) * Φ) (h1 : (e : ℝ) * Φ < 0) :
    fbar e Φ = 1 + (e : ℝ) * Φ := by
  rcases he with rfl | rfl
  · simp only [Int.cast_one, one_mul] at h0 h1 ⊢; exact fbar_one_of Φ h0 h1
  · simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at h0 h1 ⊢
    rw [fbar_m1]; rw [fbar_one_of (-Φ) h0 h1]

lemma fract_of_neg (y : ℝ) (h0 : -1 < y) (h1 : y < 0) : Int.fract y = y + 1 := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩

lemma fbar_one_half (ε Ψ : ℝ) (hε : ε < 1 / 2)
    (hΨ : (1 / 2 - ε ≤ Ψ ∧ Ψ ≤ 1 / 2 + ε) ∨ (-1 / 2 - ε ≤ Ψ ∧ Ψ ≤ -1 / 2 + ε)) :
    1 / 2 - ε ≤ fbar 1 Ψ := by
  have h0 : 0 ≤ 1 / 2 - ε := by linarith
  rcases hΨ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : Int.fract (-Ψ) = -Ψ + 1 := fract_of_neg _ (by linarith) (by linarith)
    simp only [fbar, if_true, this]; linarith
  · have : Int.fract (-Ψ) = -Ψ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    simp only [fbar, if_true, this]; linarith

lemma fbar_sign_half (e : ℤ) (he : e = 1 ∨ e = -1) (ε Ψ : ℝ) (hε : ε < 1 / 2)
    (hΨ : (1 / 2 - ε ≤ (e : ℝ) * Ψ ∧ (e : ℝ) * Ψ ≤ 1 / 2 + ε) ∨
      (-1 / 2 - ε ≤ (e : ℝ) * Ψ ∧ (e : ℝ) * Ψ ≤ -1 / 2 + ε)) :
    1 / 2 - ε ≤ fbar e Ψ := by
  rcases he with rfl | rfl
  · push_cast at hΨ; simp only [one_mul] at hΨ; exact fbar_one_half ε Ψ hε hΨ
  · push_cast at hΨ; rw [fbar_m1]
    exact fbar_one_half ε (-Ψ) hε (by rcases hΨ with ⟨h1, h2⟩ | ⟨h1, h2⟩
                                      · left; constructor <;> linarith
                                      · right; constructor <;> linarith)

lemma fbar_zero_half (ε Ψ : ℝ) (hε : ε < 1 / 2)
    (hΨ : (1 / 2 - ε ≤ Ψ ∧ Ψ ≤ 1 / 2 + ε) ∨ (-1 / 2 - ε ≤ Ψ ∧ Ψ ≤ -1 / 2 + ε)) :
    1 / 2 - ε ≤ fbar 0 Ψ := by
  have hne1 : (0 : ℤ) ≠ 1 := by norm_num
  have hne2 : (0 : ℤ) ≠ -1 := by norm_num
  rcases hΨ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : Int.fract Ψ = Ψ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    simp only [fbar, hne1, hne2, if_false, if_true, this]
    exact le_min (by linarith) (by linarith)
  · have : Int.fract Ψ = Ψ + 1 := fract_of_neg _ (by linarith) (by linarith)
    simp only [fbar, hne1, hne2, if_false, if_true, this]
    exact le_min (by linarith) (by linarith)

lemma fbar_nonneg (e : ℤ) (Φ : ℝ) : 0 ≤ fbar e Φ := by
  have h1 := Int.fract_lt_one Φ
  have h2 := Int.fract_nonneg Φ
  have h3 := Int.fract_lt_one (-Φ)
  unfold fbar
  split_ifs
  · linarith
  · linarith
  · exact le_min h2 (by linarith)
  · exact le_refl 0

end Fbar

section BS

variable {s : ℕ}

lemma stagCts_own (cs : Fin s) (a ε : ℝ) {i : Fin s} (hi : i ≠ cs) : stagCts cs a ε i i = {-a} := by
  simp [stagCts, hi]

lemma stagCts_cross (cs : Fin s) (a ε : ℝ) {i c' : Fin s} (hi : i ≠ cs) (hic : i ≠ c') :
    stagCts cs a ε i c' = Set.Icc (-ε) ε := by
  by_cases h : c' = cs
  · simp [stagCts, h, hi]
  · simp [stagCts, h, hic, hi]

lemma stagCts_cs (cs : Fin s) (a ε : ℝ) : stagCts cs a ε cs cs = {0} := by simp [stagCts]

lemma stagCts_half (cs : Fin s) (a ε : ℝ) {i : Fin s} (hi : i ≠ cs) :
    stagCts cs a ε cs i = Set.Icc (1 / 2 - ε) (1 / 2 + ε) := by
  simp [stagCts, hi, Ne.symm hi]

lemma sign_of (e : ℤ) (h1 : -1 ≤ e) (h2 : e ≤ 1) (h : e ≠ 0) : e = 1 ∨ e = -1 := by omega

/-- A moving coordinate `i ∈ C` (`thm:BS`, step (i)): `|e_i Φ_i + a| ≤ ∑_{c' ≠ i} |e_{c'}| ε`. -/
lemma bs_row (cs : Fin s) (a ε : ℝ) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (i : Fin s)
    (hi : i ≠ cs) (hei : e i ≠ 0) (x : Fin s → ℝ) (hx : ∀ c', e c' ≠ 0 → x c' ∈ stagCts cs a ε i c') :
    |(e i : ℝ) * (∑ c', (e c' : ℝ) * x c') + a| ≤ ∑ c' ∈ univ.erase i, |(e c' : ℝ)| * ε := by
  have hxi : x i = -a := by have := hx i hei; rw [stagCts_own cs a ε hi] at this; exact this
  have hei2 : (e i : ℝ) * e i = 1 := by
    rcases sign_of (e i) (he i).1 (he i).2 hei with h | h <;> rw [h] <;> norm_num
  rw [← Finset.add_sum_erase _ _ (mem_univ i), hxi]
  have : (e i : ℝ) * ((e i : ℝ) * -a + ∑ c' ∈ univ.erase i, (e c' : ℝ) * x c') + a =
      ∑ c' ∈ univ.erase i, (e i : ℝ) * ((e c' : ℝ) * x c') := by
    rw [mul_add, ← mul_assoc, hei2, Finset.mul_sum]; ring
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c' hc' => ?_)
  have hic : i ≠ c' := (Finset.ne_of_mem_erase hc').symm
  have hei' : |(e i : ℝ)| = 1 := by
    rcases sign_of (e i) (he i).1 (he i).2 hei with h | h <;> rw [h] <;> norm_num
  rw [abs_mul, abs_mul, hei', one_mul]
  by_cases h0 : e c' = 0
  · simp [h0]
  · have := hx c' h0
    rw [stagCts_cross cs a ε hi hic] at this
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨this.1, this.2⟩) (abs_nonneg _)

lemma sum_abs_le (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (i : Fin s) (ε : ℝ) (hε : 0 ≤ ε) :
    ∑ c' ∈ univ.erase i, |(e c' : ℝ)| * ε ≤ ((s : ℝ) - 1) * ε := by
  have h1 : ∑ c' ∈ univ.erase i, |(e c' : ℝ)| * ε ≤ ∑ c' ∈ univ.erase i, (1 : ℝ) * ε :=
    Finset.sum_le_sum fun c' _ => mul_le_mul_of_nonneg_right
      (abs_le.mpr ⟨by exact_mod_cast (he c').1, by exact_mod_cast (he c').2⟩) hε
  rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  rw [Nat.cast_sub hs] at h1; simpa using h1

lemma sum_ge_two (f : Fin s → ℝ) (hf : ∀ c, 0 ≤ f c) {i j : Fin s} (hij : i ≠ j) :
    f i + f j ≤ ∑ c, f c := by
  rw [← Finset.sum_pair hij]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ => hf c

/-- **`thm:BS`** (the staggered windows): let `s ≥ 2` and `a, ε > 0` with `(s-1)ε < a ≤ 1-ε` and
`(1-a-ε)² + (½-ε)² ≥ 1` (`a ≤ 1-ε` is the hypothesis `h3 : a + ε ≤ 1`). Then the staggered continuum windows
have `c*(W) ≥ 1`. -/
theorem BS (hs : 2 ≤ s) (cs : Fin s) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (h1 : ((s : ℝ) - 1) * ε < a)
    (h2 : 1 ≤ (1 - a - ε) ^ 2 + (1 / 2 - ε) ^ 2) (h3 : a + ε ≤ 1) : CtsLB (stagCts cs a ε) 1 := by
  intro e he hne Φ hΦ
  choose X hX hXe using hΦ
  refine le_trans (le_of_eq Real.sqrt_one.symm) (Real.sqrt_le_sqrt ?_)
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  -- consequences of the hypotheses
  have hεa : ε < a := by nlinarith
  have hε2 : ε < 1 / 2 := by linarith
  set q := 1 - a - ε with hq
  have hq0 : 0 ≤ q := by linarith
  have hq2 : 3 / 4 < q ^ 2 := by nlinarith
  have hq86 : 86 / 100 < q := by nlinarith
  have ha2 : 2 * a < 1 := by linarith
  have hnn : ∀ c, 0 ≤ fbar (e c) (Φ c) ^ 2 := fun c => sq_nonneg _
  -- the moving coordinates of `C`
  have hrow : ∀ i, i ≠ cs → e i ≠ 0 →
      1 - a - ∑ c' ∈ univ.erase i, |(e c' : ℝ)| * ε ≤ fbar (e i) (Φ i) := by
    intro i hi hei
    have hb := bs_row cs a ε e he i hi hei (X i) (hX i)
    have hR := sum_abs_le e he i ε hε.le
    rw [← hXe i] at hb
    set R := ∑ c' ∈ univ.erase i, |(e c' : ℝ)| * ε
    have hb' := abs_le.mp hb
    rw [fbar_sign (e i) (sign_of _ (he i).1 (he i).2 hei) (Φ i) (by linarith) (by linarith)]
    linarith
  by_cases hA : ∃ i j, i ≠ cs ∧ j ≠ cs ∧ e i ≠ 0 ∧ e j ≠ 0 ∧ i ≠ j
  · -- (ii) two moving coordinates of `C`
    obtain ⟨i, j, hi, hj, hei, hej, hij⟩ := hA
    have hfi := hrow i hi hei
    have hfj := hrow j hj hej
    have hRi := sum_abs_le e he i ε hε.le
    have hRj := sum_abs_le e he j ε hε.le
    have hb : 2 * q - 1 < 1 - a - ((s : ℝ) - 1) * ε := by linarith
    have hpos : 0 < 2 * q - 1 := by linarith
    have hfi' : 2 * q - 1 ≤ fbar (e i) (Φ i) := by linarith
    have hfj' : 2 * q - 1 ≤ fbar (e j) (Φ j) := by linarith
    have := sum_ge_two (fun c => fbar (e c) (Φ c) ^ 2) hnn hij
    have h72 : 72 / 100 < 2 * q - 1 := by linarith
    have hsq : ∀ y : ℝ, 2 * q - 1 ≤ y → (72 / 100) ^ 2 ≤ y ^ 2 := fun y hy => by nlinarith
    have := hsq _ hfi'
    have := hsq _ hfj'
    nlinarith
  · push_neg at hA
    by_cases hB : ∃ i, i ≠ cs ∧ e i ≠ 0
    · obtain ⟨i, hi, hei⟩ := hB
      have hoth : ∀ c, c ≠ cs → c ≠ i → e c = 0 := by
        intro c hc hci
        by_contra h
        exact hci (hA c i hc hi h hei)
      have hsum_cs : Φ cs = (e cs : ℝ) * X cs cs + (e i : ℝ) * X cs i := by
        have hsub : ∑ c', (e c' : ℝ) * X cs c' = ∑ c' ∈ ({cs, i} : Finset (Fin s)), (e c' : ℝ) * X cs c' := by
          refine (Finset.sum_subset (subset_univ _) fun c _ hc => ?_).symm
          simp only [mem_insert, mem_singleton, not_or] at hc
          rw [hoth c hc.1 hc.2]; simp
        rw [hXe cs, hsub, Finset.sum_pair (Ne.symm hi)]
      have hxi : X cs i ∈ Set.Icc (1 / 2 - ε) (1 / 2 + ε) := by
        have := hX cs i hei; rwa [stagCts_half cs a ε hi] at this
      have hR : ∑ c' ∈ univ.erase i, |(e c' : ℝ)| * ε = |(e cs : ℝ)| * ε := by
        rw [Finset.sum_eq_single_of_mem cs (mem_erase.mpr ⟨Ne.symm hi, mem_univ _⟩)]
        intro c hc hccs
        rw [hoth c hccs (Finset.ne_of_mem_erase hc)]; simp
      have hfi := hrow i hi hei
      rw [hR] at hfi
      rcases sign_of (e i) (he i).1 (he i).2 hei with hsi | hsi
      all_goals
      · by_cases hcs : e cs = 0
        · -- (iv) `E = {i}`
          rw [hcs] at hfi hsum_cs
          simp only [Int.cast_zero, abs_zero, zero_mul, sub_zero, zero_add] at hfi hsum_cs
          have hf0 : 1 / 2 - ε ≤ fbar (e cs) (Φ cs) := by
            rw [hcs, hsum_cs]
            refine fbar_zero_half ε _ hε2 ?_
            rw [hsi]; push_cast
            first
              | (left; constructor <;> linarith [hxi.1, hxi.2])
              | (right; constructor <;> linarith [hxi.1, hxi.2])
          have := sum_ge_two (fun c => fbar (e c) (Φ c) ^ 2) hnn hi
          have h01 : 0 ≤ 1 / 2 - ε := by linarith
          have hA1 : q ≤ fbar (e i) (Φ i) := by linarith
          nlinarith [mul_le_mul hA1 hA1 hq0 (by linarith), mul_le_mul hf0 hf0 h01 (by linarith)]
        · -- (v) `E = {i, c⋆}`
          have hcs1 := sign_of (e cs) (he cs).1 (he cs).2 hcs
          have hx0 : X cs cs = 0 := by have := hX cs cs hcs; rwa [stagCts_cs] at this
          have hecs : |(e cs : ℝ)| = 1 := by rcases hcs1 with h | h <;> rw [h] <;> norm_num
          rw [hecs, one_mul] at hfi
          rw [hx0, mul_zero, zero_add] at hsum_cs
          have hf0 : 1 / 2 - ε ≤ fbar (e cs) (Φ cs) := by
            rw [hsum_cs]
            refine fbar_sign_half (e cs) hcs1 ε _ hε2 ?_
            rw [hsi]
            rcases hcs1 with h | h <;> rw [h] <;> push_cast
            all_goals first
              | (left; constructor <;> linarith [hxi.1, hxi.2])
              | (right; constructor <;> linarith [hxi.1, hxi.2])
          have := sum_ge_two (fun c => fbar (e c) (Φ c) ^ 2) hnn hi
          have h01 : 0 ≤ 1 / 2 - ε := by linarith
          nlinarith [mul_le_mul hfi hfi hq0 (by linarith), mul_le_mul hf0 hf0 h01 (by linarith)]
    · -- (iii) `E = {c⋆}`
      push_neg at hB
      have hcs : e cs ≠ 0 := by
        obtain ⟨c, hc⟩ := hne
        by_contra h
        by_cases hcc : c = cs
        · exact hc (hcc ▸ h)
        · exact hc (hB c hcc)
      have hx0 : X cs cs = 0 := by have := hX cs cs hcs; rwa [stagCts_cs] at this
      have hΦ0 : Φ cs = 0 := by
        rw [hXe cs, Finset.sum_eq_single cs (fun c _ hc => by rw [hB c hc]; simp) (by simp), hx0,
          mul_zero]
      have hf : fbar (e cs) (Φ cs) = 1 := by
        rw [hΦ0]
        rcases sign_of (e cs) (he cs).1 (he cs).2 hcs with h | h <;> rw [h] <;> simp [fbar]
      have := Finset.single_le_sum (fun c _ => hnn c) (mem_univ cs)
      simp only [hf, one_pow] at this
      exact this

/-! ## `ε_s` -/

/-- `ε_s` is a root of `(1 - sε)² + (½ - ε)² = 1` (`thm:BS`). -/
theorem epsS_root (s : ℕ) : (1 - s * epsS s) ^ 2 + (1 / 2 - epsS s) ^ 2 = 1 := by
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (s : ℝ) ^ 2 + 4 * s by positivity)
  have hden : (0 : ℝ) < 2 * ((s : ℝ) ^ 2 + 1) := by positivity
  unfold epsS
  set d := Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s)
  field_simp
  nlinarith [hd]

lemma epsS_factor (s : ℕ) (ε : ℝ) :
    4 * ((s : ℝ) ^ 2 + 1) * ((1 - s * ε) ^ 2 + (1 / 2 - ε) ^ 2 - 1) =
      (2 * ((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1) - Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s)) *
        (2 * ((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1) + Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s)) := by
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (s : ℝ) ^ 2 + 4 * s by positivity)
  nlinarith [hd]

lemma epsS_lt_iff (s : ℕ) (ε : ℝ) :
    ε < epsS s ↔ 2 * ((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1) + Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s) < 0 := by
  have hden : (0 : ℝ) < 2 * ((s : ℝ) ^ 2 + 1) := by positivity
  unfold epsS
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> linarith

/-- `ε_s` is the smaller root: every root `ε` of `(1-sε)² + (½-ε)² = 1` has `ε ≥ ε_s`. -/
theorem epsS_least (s : ℕ) (ε : ℝ) (h : (1 - s * ε) ^ 2 + (1 / 2 - ε) ^ 2 = 1) : epsS s ≤ ε := by
  by_contra hlt
  push_neg at hlt
  have h1 := (epsS_lt_iff s ε).mp hlt
  have hd0 := Real.sqrt_nonneg (3 * (s : ℝ) ^ 2 + 4 * s)
  have hf := epsS_factor s ε
  rw [h, sub_self, mul_zero] at hf
  have h2 : 2 * ((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1) - Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s) < 0 := by linarith
  nlinarith

/-- `s ε_s ≤ ½`. -/
lemma s_epsS_le (s : ℕ) (hs : 1 ≤ s) : (s : ℝ) * epsS s ≤ 1 / 2 := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (s : ℝ) ^ 2 + 4 * s by positivity)
  have hd0 := Real.sqrt_nonneg (3 * (s : ℝ) ^ 2 + 4 * s)
  have hden : (0 : ℝ) < 2 * ((s : ℝ) ^ 2 + 1) := by positivity
  set d := Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s)
  have hkey : (s : ℝ) ^ 2 + s - 1 ≤ s * d := by
    by_contra h
    push_neg at h
    have h0 : 0 ≤ (s : ℝ) * d := by positivity
    have : ((s : ℝ) * d) ^ 2 < ((s : ℝ) ^ 2 + s - 1) ^ 2 := by nlinarith
    nlinarith
  unfold epsS
  rw [mul_div_assoc', div_le_iff₀ hden]
  nlinarith

/-- **`thm:BS`, existence**: for every `0 < ε < ε_s` there is `a > (s-1)ε` (with `a ≤ 1-ε`) satisfying the
hypotheses of `BS`; explicitly `a = (s-1)ε + G/2`, `G = (1-sε)² + (½-ε)² - 1 > 0`. -/
theorem BS_exists (s : ℕ) (hs : 2 ≤ s) (ε : ℝ) (hε : 0 < ε) (hεs : ε < epsS s) :
    ∃ a : ℝ, 0 < a ∧ ((s : ℝ) - 1) * ε < a ∧ a + ε ≤ 1 ∧ 1 ≤ (1 - a - ε) ^ 2 + (1 / 2 - ε) ^ 2 := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 := (epsS_lt_iff s ε).mp hεs
  have hd0 := Real.sqrt_nonneg (3 * (s : ℝ) ^ 2 + 4 * s)
  have hf := epsS_factor s ε
  set G := (1 - s * ε) ^ 2 + (1 / 2 - ε) ^ 2 - 1 with hG
  have hGpos : 0 < G := by
    have h2 : 2 * ((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1) - Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s) < 0 := by
      linarith
    have : 0 < 4 * ((s : ℝ) ^ 2 + 1) * G := by rw [hf]; nlinarith
    have h4 : 0 < 4 * ((s : ℝ) ^ 2 + 1) := by positivity
    exact pos_of_mul_pos_right this h4.le
  have hse : (s : ℝ) * ε < 1 / 2 := by
    have := s_epsS_le s (by omega)
    have : (s : ℝ) * ε < s * epsS s := mul_lt_mul_of_pos_left hεs (by linarith)
    linarith
  have hG4 : G ≤ 1 / 4 := by
    have : G - 1 / 4 = ε * (((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1)) := by rw [hG]; ring
    have h5 : ((s : ℝ) ^ 2 + 1) * ε - (2 * s + 1) ≤ 0 := by nlinarith
    nlinarith
  refine ⟨((s : ℝ) - 1) * ε + G / 2, by nlinarith, by linarith, by nlinarith, ?_⟩
  have hx : 0 ≤ 1 - (s : ℝ) * ε := by linarith
  have : (1 - (((s : ℝ) - 1) * ε + G / 2) - ε) ^ 2 + (1 / 2 - ε) ^ 2 =
      1 + G - G * (1 - s * ε) + (G / 2) ^ 2 := by rw [hG]; ring
  rw [this]
  nlinarith [sq_nonneg (G / 2), mul_nonneg hGpos.le (show 0 ≤ (s : ℝ) * ε by positivity)]

/-- `ε_3 = (7 - √39)/20`, and `0.0377 < ε_3 < 0.0378` (`thm:BS`). -/
theorem epsS_three : epsS 3 = (7 - Real.sqrt 39) / 20 ∧ 377 / 10000 < epsS 3 ∧ epsS 3 < 378 / 10000 := by
  have he : epsS 3 = (7 - Real.sqrt 39) / 20 := by unfold epsS; norm_num
  have h39 := Real.sq_sqrt (show (0 : ℝ) ≤ 39 by norm_num)
  have h0 := Real.sqrt_nonneg 39
  refine ⟨he, ?_, ?_⟩ <;> rw [he]
  · nlinarith
  · nlinarith

end BS

end GeoSeq
