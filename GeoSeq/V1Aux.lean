/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V1
public import GeoSeq.Kummer3

@[expose] public section

/-!
# GeoSeq stage V1 (continued): sign symmetry of `LB(W)`, `lem:volume` for column windows,
`lem:antipode`, and a non-vacuity instance of `prop:steer`

* `gapNum1_neg`, `sumsetS_neg`: the certificate term is invariant under `(e, σ) ↦ (-e, -σ)`, and
  `S_c(-e) = -S_c(e)`; so the paper's minimum over steps "up to sign" equals the minimum over all steps
  (`WinLB` quantifies over all steps).
* `steer_volume` (`lem:volume`, "in particular" clause): under (ii) of `prop:steer`,
  `|Wo^{(c')}| ∏_{c≠c'} |W_{c←c'}| ≥ p^{s-1}`.
* `fbar_neg_one`, **`antipode_f1`**, **`antipode_agree`**, `antipode_half` (`lem:antipode`).
* `steer_nonvacuous`: the hypotheses of `steer` hold for `s = 3`, `p = 7`, the Kummer frame `z³ - 1`
  (places `1, 2, 4`), `θ = 1`, `λ_c = 1` and the non-trivial windows `Wo = {0}`, `W_{c←c'} = 𝔽_7` (the strip of
  `fig:cost`(b)); a selection rule exists and gives a `(0,3)`-sequence with all responses in the windows.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Sign

lemma min'_congr_nat {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h; rfl

/-- `f_1(-e, -σ) = f_1(e, σ)` (the certificate term is invariant under reversing the step). -/
theorem gapNum1_neg (p : ℕ) [NeZero p] (e : ℤ) (σ : ZMod p) :
    gapNum1 p (-e) (-σ) = gapNum1 p e σ := by
  unfold gapNum1
  have h : (univ.image fun r : ZMod p => ((-e) * (p : ℤ) + ((r + -σ).val : ℤ) - (r.val : ℤ)).natAbs) =
      univ.image fun r : ZMod p => (e * (p : ℤ) + ((r + σ).val : ℤ) - (r.val : ℤ)).natAbs := by
    ext x
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨r - σ, ?_⟩
      rw [sub_add_cancel, ← Int.natAbs_neg, show r + -σ = r - σ by ring]
      congr 1
      ring
    · rintro ⟨r, rfl⟩
      refine ⟨r + σ, ?_⟩
      rw [show r + σ + -σ = r by ring, ← Int.natAbs_neg]
      congr 1
      ring
  exact congrArg (· - 1) (min'_congr_nat h _ _)

/-- `S_c(-e) = -S_c(e)`. -/
theorem sumsetS_neg {s p : ℕ} (W : Fin s → Fin s → Set (ZMod p)) (e : Fin s → ℤ) (c : Fin s)
    (σ : ZMod p) : -σ ∈ sumsetS W (-e) c ↔ σ ∈ sumsetS W e c := by
  constructor
  · rintro ⟨x, hx, hσ⟩
    refine ⟨x, fun c' hc' => hx c' (by simpa using hc'), ?_⟩
    have : σ = -(∑ c', (((-e) c' : ℤ) : ZMod p) * x c') := by rw [← hσ, neg_neg]
    rw [this]
    simp [Finset.sum_neg_distrib]
  · rintro ⟨x, hx, hσ⟩
    refine ⟨x, fun c' hc' => hx c' (by simpa using hc'), ?_⟩
    rw [hσ]
    simp [Finset.sum_neg_distrib]

end Sign

section Volume

/-- **`lem:volume`** for the column windows of `prop:steer` (the "in particular" clause): if condition (ii)
holds for column `c'`, then `|Wo^{(c')}| ∏_{c≠c'} |W_{c←c'}| ≥ p^{s-1}`. -/
theorem steer_volume {s : ℕ} (p : ℕ) [Fact p.Prime] (θ : ZMod p) (lamv : Fin s → ZMod p)
    (zθ : Fin s → PowerSeries (ZMod p)) (W : Fin s → Fin s → Set (ZMod p)) (c' : Fin s)
    (hii : LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    p ^ (s - 1) ≤ (W c' c').ncard * ∏ c ∈ univ.erase c', (W c c').ncard := by
  classical
  have hα : stAlpha θ lamv zθ c' ≠ 0 := by
    intro h
    have := congrFun h c'
    simp [stAlpha] at this
  have hupd : Function.update (fun c => (W c c').toFinset) c' (W c' c').toFinset =
      fun c => (W c c').toFinset := Function.update_eq_self c' _
  have hc := cover_prod (stAlpha θ lamv zθ c') hα c' (W c' c').toFinset (fun c => (W c c').toFinset)
    (by
      intro β
      obtain ⟨t, ht⟩ := hii β
      refine ⟨t, ?_⟩
      rw [hupd, Fintype.mem_piFinset]
      intro c
      rw [Set.mem_toFinset]
      exact ht c)
  rw [ZMod.card] at hc
  simpa only [Set.ncard_eq_toFinset_card'] using hc

end Volume

section Antipode

/-- `f̄(-1, Φ) = f̄(+1, -Φ)` (`lem:antipode`). -/
theorem fbar_neg_one (Φ : ℝ) : fbar (-1) Φ = fbar 1 (-Φ) := by
  simp [fbar]

lemma fract_val_div (p : ℕ) [NeZero p] (σ : ZMod p) :
    Int.fract ((σ.val : ℝ) / p) = (σ.val : ℝ) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [Int.fract_eq_self]
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hp]
  exact_mod_cast ZMod.val_lt σ

/-- **`lem:antipode`** (one geometric digit): for `σ ∈ ℤ/pℤ` and `Φ = σ/p ∈ ℝ/ℤ` (representative
`val σ / p`), `f_1(e, σ) = max(0, f̄(e, Φ) - 1/p)` for `e ∈ {-1, 0, 1}`. -/
theorem antipode_f1 (p : ℕ) [NeZero p] (e : ℤ) (he : e = -1 ∨ e = 0 ∨ e = 1) (σ : ZMod p) :
    (gapNum1 p e σ : ℝ) / p = max 0 (fbar e ((σ.val : ℝ) / p) - 1 / p) := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hp : (0 : ℝ) < p := by exact_mod_cast hp0
  have hv : σ.val < p := ZMod.val_lt σ
  have hfr := fract_val_div p σ
  rcases he with rfl | rfl | rfl
  · -- `e = -1`
    have h1 : gapNum1 p (-1) σ = gapNum1 p 1 (-σ) := by
      rw [← gapNum1_neg p 1 (-σ), neg_neg]
    rw [h1, f1_one_val]
    simp only [fbar, show (-1 : ℤ) ≠ 1 by norm_num, if_false, if_true, hfr]
    by_cases hσ : σ = 0
    · subst hσ
      simp only [neg_zero, if_true, ZMod.val_zero, Nat.cast_zero, zero_div, sub_zero]
      rw [Nat.cast_sub (by omega), Nat.cast_one, max_eq_right]
      · field_simp
      · rw [sub_nonneg, div_le_one hp]; exact_mod_cast hp0
    · have hn : -σ ≠ 0 := neg_ne_zero.2 hσ
      have hv1 : 1 ≤ σ.val := Nat.one_le_iff_ne_zero.2 ((ZMod.val_ne_zero σ).2 hσ)
      have : NeZero σ := ⟨hσ⟩
      rw [if_neg hn, ZMod.val_neg_of_ne_zero σ, Nat.cast_sub (by omega), Nat.cast_sub hv.le,
        Nat.cast_one, max_eq_right]
      · field_simp
      · rw [sub_sub, sub_nonneg, ← add_div, div_le_one hp]
        have : (σ.val : ℝ) + 1 ≤ p := by exact_mod_cast hv
        linarith
  · -- `e = 0`
    rw [f1_zero_val]
    simp only [fbar, show (0 : ℤ) ≠ 1 by norm_num, show (0 : ℤ) ≠ -1 by norm_num, if_false, if_true,
      hfr]
    by_cases hσ : σ = 0
    · subst hσ
      simp only [ZMod.val_zero, Nat.zero_sub, Nat.sub_zero, zero_le, min_eq_left, Nat.cast_zero,
        zero_div, sub_zero]
      rw [min_eq_left (by norm_num), max_eq_left (by rw [zero_sub, neg_nonpos]; positivity)]
    · have hv1 : 1 ≤ σ.val := Nat.one_le_iff_ne_zero.2 ((ZMod.val_ne_zero σ).2 hσ)
      have hm1 : 1 ≤ min σ.val (p - σ.val) := le_min hv1 (by omega)
      rw [Nat.cast_sub hm1, Nat.cast_min, Nat.cast_sub hv.le, Nat.cast_one]
      have e1 : min ((σ.val : ℝ) / p) (1 - (σ.val : ℝ) / p) = min (σ.val : ℝ) (p - σ.val) / p := by
        rw [show 1 - (σ.val : ℝ) / p = (p - σ.val) / p by field_simp, min_div_div_right hp.le]
      rw [e1, max_eq_right]
      · field_simp
      · rw [← sub_div]
        apply div_nonneg _ hp.le
        rw [sub_nonneg]
        have := hm1
        rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_sub hv.le, ← Nat.cast_min]
        exact_mod_cast hm1
  · -- `e = 1`
    rw [f1_one_val]
    simp only [fbar, if_true]
    by_cases hσ : σ = 0
    · subst hσ
      simp only [if_true, ZMod.val_zero, Nat.cast_zero, zero_div, neg_zero, Int.fract_zero, sub_zero]
      rw [Nat.cast_sub (by omega), Nat.cast_one, max_eq_right]
      · field_simp
      · rw [sub_nonneg, div_le_one hp]; exact_mod_cast hp0
    · have hv1 : 1 ≤ σ.val := Nat.one_le_iff_ne_zero.2 ((ZMod.val_ne_zero σ).2 hσ)
      have hne : Int.fract ((σ.val : ℝ) / p) ≠ 0 := by
        rw [hfr]; positivity
      rw [if_neg hσ, Int.fract_neg hne, hfr, Nat.cast_sub hv1, Nat.cast_one, max_eq_right]
      · field_simp; ring
      · rw [sub_sub_cancel, sub_nonneg, div_le_div_iff_of_pos_right hp]
        exact_mod_cast hv1

/-- **`lem:antipode`, the antipode**: the three functions `f̄(+1, ·)`, `f̄(-1, ·)`, `f̄(0, ·)` agree at `Φ`
exactly when `Φ ≡ 1/2 (mod 1)`. -/
theorem antipode_agree (Φ : ℝ) :
    (fbar 1 Φ = fbar (-1) Φ ∧ fbar (-1) Φ = fbar 0 Φ) ↔ Int.fract Φ = 1 / 2 := by
  have h0 := Int.fract_nonneg Φ
  have h1 := Int.fract_lt_one Φ
  simp only [fbar, if_true, show (-1 : ℤ) ≠ 1 by norm_num, show (0 : ℤ) ≠ 1 by norm_num,
    show (0 : ℤ) ≠ -1 by norm_num, if_false]
  by_cases hz : Int.fract Φ = 0
  · rw [Int.fract_neg_eq_zero.2 hz, hz]
    norm_num
  · rw [Int.fract_neg hz]
    constructor
    · rintro ⟨h, -⟩
      linarith
    · intro h
      rw [h]
      norm_num

/-- **`lem:antipode`**: at `Φ ≡ 1/2` all three functions equal `1/2`. -/
theorem antipode_half (Φ : ℝ) (h : Int.fract Φ = 1 / 2) :
    fbar 1 Φ = 1 / 2 ∧ fbar (-1) Φ = 1 / 2 ∧ fbar 0 Φ = 1 / 2 := by
  have hz : Int.fract Φ ≠ 0 := by rw [h]; norm_num
  simp only [fbar, if_true, show (-1 : ℤ) ≠ 1 by norm_num, show (0 : ℤ) ≠ 1 by norm_num,
    show (0 : ℤ) ≠ -1 by norm_num, if_false, Int.fract_neg hz, h]
  norm_num

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
  have hp3 : 7 % 3 = 1 := by norm_num
  obtain ⟨hτ0, hτ3⟩ := kumTau_facts 7 hp3 1
  have hmon : (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]).Monic :=
    Polynomial.monic_X_pow_sub_C 1 (by norm_num)
  have hdeg : (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]).natDegree = 3 :=
    Polynomial.natDegree_X_pow_sub_C
  have h8 : ∀ c : Fin 3, ((2 : ZMod 7) ^ (c : ℕ)) ^ 3 = 1 := by decide
  have hroot : ∀ c, Polynomial.aeval (kumZ 7 2 1 c) (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]) =
      C 1 * X := by
    intro c
    have e : Polynomial.aeval (kumZ 7 2 1 c) (Polynomial.X ^ 3 - Polynomial.C 1 : (ZMod 7)[X]) =
        (kumZ 7 2 1 c) ^ 3 - 1 := by simp
    rw [e]
    simp only [kumZ]
    rw [mul_pow, hτ3, ← map_pow, h8 c, map_one]
    ring
  have hpl : ∀ c, ssPlace (kumZ 7 2 1) c = (2 : ZMod 7) ^ (c : ℕ) := by
    intro c; simp [ssPlace, kumZ, hτ0]
  have hinj : Function.Injective (ssPlace (kumZ 7 2 1)) := by
    intro x y hxy
    rw [hpl, hpl] at hxy
    revert x y
    decide
  have hi : ∀ c c' : Fin 3, c ≠ c' → -kapL 1 (fun _ => 1) (kumZ 7 2 1) c c' ∈ stripWin 0 c c' := by
    intro c c' hc
    simp [stripWin, hc]
  have hii : ∀ c', LinesMeet (stAlpha 1 (fun _ => (1 : ZMod 7)) (kumZ 7 2 1) c')
      (colWin (stripWin 0) c') := by
    intro c' β
    refine ⟨-β c', fun c => ?_⟩
    by_cases hc : c = c'
    · subst hc; simp [stripWin, stAlpha]; exact add_neg_cancel _
    · simp [stripWin, hc]
  obtain ⟨-, ⟨rule, hrule⟩, hall⟩ := steer 7 (by norm_num) _ hmon hdeg 1 one_ne_zero _ hroot hinj
    (fun _ => 1) (fun _ => one_ne_zero) (stripWin 0) hi hii
  obtain ⟨-, hseq, hresp, -⟩ := hall rule hrule
  exact ⟨hmon, hdeg, hroot, hinj, hi, hii, rule, hrule, hseq, hresp⟩

end NonVacuous

end GeoSeq
