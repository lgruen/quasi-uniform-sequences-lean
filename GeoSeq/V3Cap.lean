/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Range

@[expose] public section

/-!
# GeoSeq stage V3: the limit of ordered windows (`prop:lexcap`)

`lexcap`: for product windows in the order `0 < ⋯ < s-1` (`s = n + 1 ≥ 2`) with every lower cross full, every
upper cross containing `0` and nonempty own windows, if the last column satisfies condition (ii) of
`prop:steer`, then every lower bound `LB` of the window bound (`WinLB`) satisfies
`LB ≤ 1 - (M_{s-1} ∏_{c<s-1} |W_{c←s-1}|)^{1/s}/p ≤ 1 - p^{-1/s}`. Proof as in the paper: the axis step of the
last coordinate and the steps moving it together with one other coordinate, distinct representatives
(`exists_gap_le`), and `lem:volume` (`steer_volume`).
-/

namespace GeoSeq

open Finset

section Cap

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p f_1(1, σ) = r(σ) - 1` with `r(σ) ∈ {1, …, p}` the representative of `σ` (`rem:onedigit`). -/
lemma gap1_add_one (σ : ZMod p) : gapNum1 p 1 σ + 1 = (if σ = 0 then p else σ.val) := by
  rw [f1_one_val]
  have : 1 ≤ (if σ = 0 then p else σ.val) := by
    split_ifs with h
    · exact hp.out.one_lt.le
    · exact Nat.pos_of_ne_zero fun h' => h ((ZMod.val_eq_zero σ).mp h')
  omega

lemma rep_le (σ : ZMod p) : (if σ = 0 then p else σ.val) ≤ p := by
  split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt σ).le

lemma rep_inj : Function.Injective (fun σ : ZMod p => if σ = 0 then p else σ.val) := by
  intro σ τ h
  simp only at h
  split_ifs at h with h1 h2 h2
  · rw [h1, h2]
  · exact absurd h (ne_of_gt (ZMod.val_lt τ))
  · exact absurd h (ne_of_lt (ZMod.val_lt σ))
  · exact ZMod.val_injective p h

/-- **Distinct representatives** (proof of `prop:lexcap`): a nonempty `S ⊆ 𝔽_p` has an element with
`p f_1(1, σ) ≤ p - |S|`. -/
lemma exists_gap_le (S : Set (ZMod p)) (hS : S.Nonempty) :
    ∃ σ ∈ S, (gapNum1 p 1 σ : ℝ) ≤ p - S.ncard := by
  classical
  set T : Finset (ZMod p) := S.toFinite.toFinset with hT
  set r : ZMod p → ℕ := fun σ => if σ = 0 then p else σ.val with hr
  have hTne : (T.image r).Nonempty := by
    obtain ⟨x, hx⟩ := hS; exact ⟨r x, mem_image_of_mem r (by simpa [hT] using hx)⟩
  obtain ⟨σ, hσT, hσm⟩ := mem_image.mp ((T.image r).min'_mem hTne)
  refine ⟨σ, by simpa [hT] using hσT, ?_⟩
  have hcard : (T.image r).card = S.ncard := by
    rw [card_image_of_injective _ rep_inj, Set.ncard_eq_toFinset_card S]
  have hsub : T.image r ⊆ Icc ((T.image r).min' hTne) p := fun y hy => by
    refine mem_Icc.mpr ⟨min'_le _ _ hy, ?_⟩
    obtain ⟨x, -, rfl⟩ := mem_image.mp hy
    exact rep_le x
  have h1 := card_le_card hsub
  rw [Nat.card_Icc, hcard] at h1
  have h2 := gap1_add_one σ
  have h3 : r σ = (T.image r).min' hTne := hσm
  have h4 : (if σ = 0 then p else σ.val) = r σ := rfl
  have h5 := rep_le σ
  have hle : gapNum1 p 1 σ + S.ncard ≤ p := by omega
  have : ((gapNum1 p 1 σ + S.ncard : ℕ) : ℝ) ≤ p := by exact_mod_cast hle
  push_cast at this; linarith

/-- A window bound with only one nonzero term. -/
lemma winLB_single {s : ℕ} (W : Fin s → Fin s → Set (ZMod p)) (LB : ℝ) (hLB : WinLB p W LB)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (σ : Fin s → ZMod p)
    (hσ : ∀ c, σ c ∈ sumsetS W e c) (c0 : Fin s) (hz : ∀ c, c ≠ c0 → gapNum1 p (e c) (σ c) = 0) :
    LB ≤ (gapNum1 p (e c0) (σ c0) : ℝ) / p := by
  have h := hLB e he hne σ hσ
  rw [Finset.sum_eq_single c0 (fun c _ hc => by rw [hz c hc]; simp) (fun h => absurd (mem_univ c0) h),
    Real.sqrt_sq (by positivity)] at h
  exact h

lemma gap_zero_zero : gapNum1 p 0 (0 : ZMod p) = 0 := by rw [gapNum1_zero]; simp

lemma gap_one_one : gapNum1 p 1 (1 : ZMod p) = 0 := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [f1_one_val, if_neg one_ne_zero, ZMod.val_one]

/-- **`prop:lexcap`** (the limit of ordered windows). Let `s = n + 1 ≥ 2` and let `W` be product windows such
that, in the order `0 < ⋯ < s-1`, every lower cross window is `𝔽_p`, every upper cross window contains `0`, and
the own windows are nonempty (`M_c = |Wo^{(c)}|`). If the last column satisfies condition (ii) of
`prop:steer`, then every `LB` with `WinLB p W LB` (in particular `LB(W)`) satisfies
`LB ≤ 1 - (M_{s-1} ∏_{c<s-1} |W_{c←s-1}|)^{1/s}/p ≤ 1 - p^{-1/s}`. -/
theorem lexcap (n : ℕ) (hn : 1 ≤ n) (θ : ZMod p) (lamv : Fin (n + 1) → ZMod p)
    (zθ : Fin (n + 1) → PowerSeries (ZMod p)) (W : Fin (n + 1) → Fin (n + 1) → Set (ZMod p))
    (hlow : ∀ c c' : Fin (n + 1), c' < c → W c c' = Set.univ)
    (hup : ∀ c c' : Fin (n + 1), c < c' → (0 : ZMod p) ∈ W c c')
    (hown : ∀ c, (W c c).Nonempty)
    (hii : LinesMeet (stAlpha θ lamv zθ (Fin.last n)) (colWin W (Fin.last n)))
    (LB : ℝ) (hLB : WinLB p W LB) :
    LB ≤ 1 - (((W (Fin.last n) (Fin.last n)).ncard *
        ∏ c ∈ univ.erase (Fin.last n), (W c (Fin.last n)).ncard : ℕ) : ℝ) ^ ((1 : ℝ) / (n + 1)) / p ∧
      1 - (((W (Fin.last n) (Fin.last n)).ncard *
        ∏ c ∈ univ.erase (Fin.last n), (W c (Fin.last n)).ncard : ℕ) : ℝ) ^ ((1 : ℝ) / (n + 1)) / p ≤
        1 - (p : ℝ) ^ (-(1 : ℝ) / (n + 1)) := by
  classical
  set L : Fin (n + 1) := Fin.last n with hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set t : ℝ := p * (1 - LB) with ht
  -- (A) the axis step of the last coordinate: `M_{s-1} ≤ t`
  have hA : ((W L L).ncard : ℝ) ≤ t := by
    obtain ⟨σL, hσL, hgap⟩ := exists_gap_le (W L L) (hown L)
    set e : Fin (n + 1) → ℤ := fun c => if c = L then 1 else 0 with he
    set σ : Fin (n + 1) → ZMod p := fun c => if c = L then σL else 0 with hσd
    have hmem : ∀ c, σ c ∈ sumsetS W e c := by
      intro c
      refine ⟨fun _ => σ c, fun c' hc' => ?_, ?_⟩
      · have hc'L : c' = L := by by_contra h; exact hc' (by simp [he, h])
        subst hc'L
        by_cases hcL : c = L
        · subst hcL; simpa [hσd] using hσL
        · simp only [hσd, if_neg hcL]
          exact hup c L (lt_of_le_of_ne (Fin.le_last c) hcL)
      · simp [he, Finset.sum_ite_eq']
    have hb := winLB_single W LB hLB e (fun c => by simp only [he]; split_ifs <;> norm_num)
      ⟨L, by simp [he]⟩ σ hmem L (fun c hc => by simp [he, hσd, hc, gap_zero_zero])
    have e0 : e L = 1 := by simp [he]
    have s0 : σ L = σL := by simp [hσd]
    rw [e0, s0] at hb
    rw [le_div_iff₀ hp0] at hb
    rw [ht]; nlinarith
  -- (B) the steps `1_c + 1_{s-1}`: `|W_{c←s-1}| ≤ t`
  have hB : ∀ c0 ∈ univ.erase L, ((W c0 L).ncard : ℝ) ≤ t := by
    intro c0 hc0
    have hc0L : c0 ≠ L := ne_of_mem_erase hc0
    have hc0lt : c0 < L := lt_of_le_of_ne (Fin.le_last c0) hc0L
    obtain ⟨o, ho⟩ := hown c0
    obtain ⟨o', ho'⟩ := hown L
    obtain ⟨σ0, hσ0, hgap⟩ := exists_gap_le ((fun y => o + y) '' W c0 L)
      ⟨o + 0, 0, hup c0 L hc0lt, rfl⟩
    rw [Set.ncard_image_of_injective _ (add_right_injective o)] at hgap
    obtain ⟨y0, hy0, rfl⟩ := hσ0
    set e : Fin (n + 1) → ℤ := fun c => if c = c0 ∨ c = L then 1 else 0 with he
    set σ : Fin (n + 1) → ZMod p := fun c => if c = c0 then o + y0 else if c = L then 1 else 0 with hσd
    have hsum : ∀ x : Fin (n + 1) → ZMod p, ∑ c', (e c' : ZMod p) * x c' = x c0 + x L := by
      intro x
      rw [Fintype.sum_eq_add c0 L hc0L (fun c hc => by simp [he, hc.1, hc.2])]
      simp [he]
    have hmem : ∀ c, σ c ∈ sumsetS W e c := by
      intro c
      by_cases hcc0 : c = c0
      · subst hcc0
        refine ⟨fun c' => if c' = c then o else y0, fun c' hc' => ?_, ?_⟩
        · have : c' = c ∨ c' = L := by by_contra h; exact hc' (by simp [he, h])
          rcases this with rfl | rfl
          · simpa using ho
          · simpa [hc0L.symm] using hy0
        · rw [hsum]; simp [hσd, hc0L.symm]
      · by_cases hcL : c = L
        · rw [hcL]
          refine ⟨fun c' => if c' = c0 then 1 - o' else o', fun c' hc' => ?_, ?_⟩
          · show (if c' = c0 then 1 - o' else o') ∈ W L c'
            by_cases h1 : c' = c0
            · rw [if_pos h1, h1, hlow L c0 hc0lt]; trivial
            · have h2 : c' = L := by by_contra h; exact hc' (by simp [he, h, h1])
              rw [if_neg h1, h2]; exact ho'
          · rw [hsum]
            have e1 : σ L = 1 := by simp [hσd, hc0L.symm]
            rw [e1]; simp [hc0L.symm]
        · refine ⟨fun _ => 0, fun c' hc' => ?_, ?_⟩
          · have : c' = c0 ∨ c' = L := by by_contra h; exact hc' (by simp [he, h])
            rcases this with rfl | rfl
            · rcases lt_or_gt_of_ne hcc0 with h | h
              · exact hup c c' h
              · rw [hlow c c' h]; trivial
            · exact hup c L (lt_of_le_of_ne (Fin.le_last c) hcL)
          · rw [hsum]; simp [hσd, hcc0, hcL]
    have hb := winLB_single W LB hLB e (fun c => by simp only [he]; split_ifs <;> norm_num)
      ⟨L, by simp [he]⟩ σ hmem c0 (fun c hc => by
        by_cases hcL : c = L
        · subst hcL; simp [he, hσd, hc0L.symm, gap_one_one]
        · simp [he, hσd, hc, hcL, gap_zero_zero])
    have e0 : e c0 = 1 := by simp [he]
    have s0 : σ c0 = o + y0 := by simp [hσd]
    rw [e0, s0] at hb
    rw [le_div_iff₀ hp0] at hb
    rw [ht]; nlinarith
  -- the product bound
  set P : ℕ := (W L L).ncard * ∏ c ∈ univ.erase L, (W c L).ncard with hP
  have hM1 : (1 : ℝ) ≤ (W L L).ncard := by
    have := (Set.ncard_pos (Set.toFinite _)).mpr (hown L); exact_mod_cast this
  have ht0 : 0 ≤ t := le_trans zero_le_one (hM1.trans hA)
  have hPt : (P : ℝ) ≤ t ^ (n + 1) := by
    rw [hP]; push_cast
    have hcard : (univ.erase L).card = n := by simp
    have hprod : ∏ c ∈ univ.erase L, ((W c L).ncard : ℝ) ≤ t ^ n := by
      calc ∏ c ∈ univ.erase L, ((W c L).ncard : ℝ) ≤ ∏ c ∈ univ.erase L, t :=
            prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hB
        _ = t ^ n := by rw [prod_const, hcard]
    rw [pow_succ']
    exact mul_le_mul hA hprod (prod_nonneg fun _ _ => Nat.cast_nonneg _) ht0
  have hs1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hroot : (P : ℝ) ^ ((1 : ℝ) / (n + 1)) ≤ t := by
    calc (P : ℝ) ^ ((1 : ℝ) / (n + 1)) ≤ (t ^ (n + 1)) ^ ((1 : ℝ) / (n + 1)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hPt (by positivity)
      _ = t := by
          rw [one_div, ← Real.rpow_natCast, ← Real.rpow_mul ht0]; push_cast
          rw [mul_inv_cancel₀ hs1, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rw [le_sub_comm, div_le_iff₀ hp0]
    rw [ht] at hroot; linarith
  · -- `P ≥ p^n` (`lem:volume`)
    have hvol := steer_volume p θ lamv zθ W L hii
    simp only [Nat.add_sub_cancel] at hvol
    have hPn : ((p : ℝ) ^ n) ≤ P := by rw [hP]; exact_mod_cast hvol
    have h1 : ((p : ℝ) ^ n) ^ ((1 : ℝ) / (n + 1)) ≤ (P : ℝ) ^ ((1 : ℝ) / (n + 1)) :=
      Real.rpow_le_rpow (by positivity) hPn (by positivity)
    have h2 : ((p : ℝ) ^ n) ^ ((1 : ℝ) / (n + 1)) / p = (p : ℝ) ^ (-(1 : ℝ) / (n + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, div_eq_mul_inv, ← Real.rpow_neg_one,
        ← Real.rpow_add hp0]
      congr 1
      field_simp
      ring
    have h3 : ((p : ℝ) ^ n) ^ ((1 : ℝ) / (n + 1)) / p ≤ (P : ℝ) ^ ((1 : ℝ) / (n + 1)) / p :=
      div_le_div_of_nonneg_right h1 hp0.le
    linarith

/-- **The mixed-radix rule attains the rate** (after `prop:lexcap`): `MR(s,p,h)` with `Γ < p` lies in the class
of `prop:lexcap`, so `1 - (p - Γ)/p ≥ p^{-1/s}` (`s = n + 1 ≥ 2`, `p ≥ s` prime, `h_t ≥ 1`); with `MRall_c`,
`p^{-1/s} ≤ 1 - LB(W) ≤ C'_s p^{-1/s}` for the mixed-radix rule. -/
theorem MR_cap (n p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (hsp : n + 1 ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ n + 1 - 1 → 1 ≤ h t) (hΓ : mrCost (n + 1) p h < p) :
    (p : ℝ) ^ (-(1 : ℝ) / (n + 1)) ≤ 1 - ((p : ℝ) - mrCost (n + 1) p h) / p := by
  set zθ : Fin (n + 1) → PowerSeries (ZMod p) := fun c => PowerSeries.C ((c : ℕ) : ZMod p) with hz
  have hplace : ∀ c, PowerSeries.constantCoeff (zθ c) = ((c : ℕ) : ZMod p) := fun c => by simp [hz]
  have hii := MR_cond_ii (n + 1) p (by omega) hsp h hh hΓ zθ hplace (Fin.last n)
  have hLB := (MR_LB (n + 1) p (by omega) h hh hΓ).1
  have hlow : ∀ c c' : Fin (n + 1), c' < c → mrWin (n + 1) p h c c' = Set.univ := fun c c' hcc => by
    unfold mrWin lexWin; rw [if_pos hcc]
  have hup : ∀ c c' : Fin (n + 1), c < c' → (0 : ZMod p) ∈ mrWin (n + 1) p h c c' := fun c c' hcc => by
    unfold mrWin lexWin
    rw [if_neg (not_lt.mpr hcc.le), if_pos hcc]
    exact ⟨0, by simp, by simp, by simp⟩
  have hown : ∀ c, (mrWin (n + 1) p h c c).Nonempty := fun c => by
    have hM := mrM_pos (s := n + 1) (p := p) (h := h) (by omega) (by omega) hh c c.isLt
    unfold mrWin lexWin
    rw [if_neg (lt_irrefl c), if_neg (lt_irrefl c)]
    refine ⟨_, -(mrB (n + 1) p h c : ℤ), ?_, le_rfl, rfl⟩
    push_cast; omega
  have := (lexcap n hn (mrTheta (n + 1) p) (mrLam (n + 1) p h) zθ (mrWin (n + 1) p h) hlow hup hown hii
    _ hLB)
  linarith [this.1, this.2]

end Cap

end GeoSeq
