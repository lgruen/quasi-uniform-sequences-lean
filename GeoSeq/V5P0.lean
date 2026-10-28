/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Mono
public import GeoSeq.V5W
public import GeoSeq.V5Cover
public import GeoSeq.V5R

@[expose] public section

/-!
# GeoSeq stage V5: the threshold proposition (`prop:P0`(a) and its consequence)

At a prime `p` with `𝒫(p)` (real `p`), the staggered rule (`def:BS`) with crosses `κ_{c←c'} = T n_{cc'}`:
* **`P0_cond_i`**: condition (i) of `prop:steer` (`-κ_{c←c'} ∈ W_{c←c'}`, the half-cell offsets near `½`);
* **`P0_cond_ii`**: condition (ii) (column `c⋆` by `lem:ws`, every other column doubled, `lem:D`);
* **`P0_W`**: the hypotheses of `lem:W` including its last statement, and `M⋆ ≤ M⋆^+(p)`;
* **`P0_a`** = all of `prop:P0`(a); **`P0_seq`** = the consequence of `prop:P0` (with `P0_mono`): if `𝒫(p₀)`, then
  for every prime `p ≥ p₀` every selection rule gives a quasi-uniform digital `(0,s)`-sequence with
  `c(P_{sK}) ≥ 1 - M⋆^+(p₀)/p` (and `≥ 1 - C/p` for every integer `C > M⋆^+(p₀) - 1`, as `M⋆` is an integer);
* **`P0_design`**: the same for the staggered rule of a staggered design (`lem:R` supplies the crosses).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Facts

/-- (S1): `T` is odd, `1 ≤ T`, and `up - 2 < T ≤ up` (when `up > 2`). -/
lemma stT_facts (u : ℚ) (p : ℕ) (h : 2 < (u : ℝ) * p) :
    1 ≤ stT u p ∧ stT u p % 2 = 1 ∧ (stT u p : ℝ) ≤ u * p ∧ (u : ℝ) * p - 2 < stT u p := by
  have hq : (2 : ℚ) < u * p := by exact_mod_cast h
  have h0 : (0 : ℚ) ≤ u * p := by linarith
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (u * (p : ℚ))
  set f := ⌊u * (p : ℚ)⌋₊ with hf
  have h1' : (f : ℝ) ≤ u * p := by exact_mod_cast h1
  have h2' : (u : ℝ) * p < f + 1 := by exact_mod_cast h2
  have hf2 : 2 ≤ f := by
    have : (1 : ℝ) < f := by linarith
    exact_mod_cast this
  unfold stT
  rw [← hf]
  split_ifs with hodd
  · exact ⟨by omega, hodd, h1', by linarith⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have : ((f - 1 : ℕ) : ℝ) = f - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; linarith
    · have : ((f - 1 : ℕ) : ℝ) = f - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; linarith

/-- (S2): `εp - 1 < B`, and `B ≤ εp` for `ε ≥ 0`. -/
lemma stB_facts (e : ℚ) (p : ℕ) : (e : ℝ) * p - 1 < stB e p ∧ (0 ≤ e → (stB e p : ℝ) ≤ e * p) := by
  unfold stB
  refine ⟨?_, fun he => ?_⟩
  · have := Nat.lt_floor_add_one (e * (p : ℚ))
    have : (e : ℝ) * p < ⌊e * (p : ℚ)⌋₊ + 1 := by exact_mod_cast this
    linarith
  · have := Nat.floor_le (mul_nonneg he (Nat.cast_nonneg p : (0 : ℚ) ≤ p))
    exact_mod_cast this

/-- `⌈a/b⌉ ≤ a/b + 1`. -/
lemma cdiv_le_add_one (a b : ℕ) (hb : 1 ≤ b) : (cdiv a b : ℝ) ≤ a / b + 1 := by
  unfold cdiv
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h := Nat.div_mul_le_self (a + b - 1) b
  have h' : (((a + b - 1) / b : ℕ) : ℝ) * b ≤ ((a + b - 1 : ℕ) : ℝ) := by exact_mod_cast h
  have h3 : ((a + b - 1 : ℕ) : ℝ) = a + b - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h3] at h'
  have : (((a + b - 1) / b : ℕ) : ℝ) ≤ (a + b - 1) / b := by rw [le_div_iff₀ hbR]; exact h'
  calc (((a + b - 1) / b : ℕ) : ℝ) ≤ (a + b - 1) / b := this
    _ = a / b + 1 - 1 / b := by field_simp
    _ ≤ a / b + 1 := by have : (0 : ℝ) ≤ 1 / b := by positivity
                        linarith

lemma exists_ne_cs {s : ℕ} (cs : Fin s) (hs : 2 ≤ s) : ∃ c, c ≠ cs := by
  have : 0 < (univ.erase cs).card := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp this
  exact ⟨a, ne_of_mem_erase ha⟩

lemma exists_two_ne_cs {s : ℕ} (cs : Fin s) (hs : 3 ≤ s) : ∃ c c', c ≠ cs ∧ c' ≠ cs ∧ c ≠ c' := by
  have : 1 < (univ.erase cs).card := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
  exact ⟨a, b, ne_of_mem_erase ha, ne_of_mem_erase hb, hab⟩

end Facts

section Data

variable {s : ℕ}

lemma valid_coef (D : StagData s) (hv : D.Valid) (c' : Fin s) {t : ℕ} (ht : t < s - 1) :
    1 ≤ stCoef D c' (D.rows c' t) := by
  have h1 := hv.1 c' t ht
  have h2 := hv.2.2.1 (D.rows c' t) c' h1
  have : 1 ≤ (D.nI (D.rows c' t) c').natAbs := Int.natAbs_pos.mpr h2
  unfold stCoef; split_ifs <;> omega

lemma valid_rows (D : StagData s) (hv : D.Valid) {c c' : Fin s} (h : c ≠ c') :
    ∃ t < s - 1, D.rows c' t = c := by
  have := hv.2.1 c' c h
  obtain ⟨t, ht, he⟩ := List.mem_map.mp this
  exact ⟨t, List.mem_range.mp ht, he⟩

lemma stFrac_cs (D : StagData s) (r : Fin s) : stFrac D D.cs r = D.eCS := by simp [stFrac]

lemma stFrac_i (D : StagData s) {i : Fin s} (hi : i ≠ D.cs) (r : Fin s) :
    stFrac D i r = if r = D.cs then D.eSC else D.eCC := by simp [stFrac, hi]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The window fractions that occur are positive under `𝒫` (and `p > 0`). -/
lemma StP_eps (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) {p : K} (hp : 0 < p) (hP : StP D p) :
    0 < D.eCS ∧ 0 < D.eSC ∧ (3 ≤ s → 0 < D.eCC) := by
  obtain ⟨hP1, -, hP3, hP3h, -⟩ := hP
  have hu0 : 0 < (D.u : K) := u_pos_of _ _ hp hP1
  obtain ⟨c, hc⟩ := exists_ne_cs D.cs hs
  have hn : ∀ c c' : Fin s, c ≠ c' → (1 : K) ≤ ((D.nI c c').natAbs : K) := fun c c' h => by
    exact_mod_cast Int.natAbs_pos.mpr (hv.2.2.1 c c' h)
  have key : ∀ (f : ℚ) (n : K) (b : K), 1 ≤ n → 0 ≤ b → n * ((D.u : K) * p) ≤ (f : K) * p - b →
      (0 : ℚ) < f := by
    intro f n b hn1 hb h
    have : (0 : K) < (f : K) := coef_pos_of _ p 2 hp (by norm_num) (by nlinarith)
    exact_mod_cast this
  refine ⟨?_, ?_, fun h3 => ?_⟩
  · have := hP3 c D.cs hc hc
    rw [stFrac_cs] at this
    exact key _ _ 1 (hn _ _ hc) zero_le_one this
  · have := hP3h c hc
    have h2 : (0 : ℚ) < 2 * D.eSC := key (2 * D.eSC) _ 3 (hn _ _ (Ne.symm hc)) (by norm_num) (by push_cast; linarith)
    linarith
  · obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne_cs D.cs h3
    have := hP3 a b ha hab
    rw [stFrac_i D hb, if_neg ha] at this
    exact key _ _ 1 (hn _ _ hab) zero_le_one this

end Data

section Prime

variable {s : ℕ} {p : ℕ} [Fact p.Prime]

lemma three_le_of {a b c : Fin s} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s := by
  have h : ({a, b, c} : Finset (Fin s)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  have := Finset.card_le_univ ({a, b, c} : Finset (Fin s))
  rw [h, Fintype.card_fin] at this
  exact this

lemma arc_sub_intWin (L : ℤ) (len : ℕ) (x : ZMod p) (hx : x ∈ arc p L len) :
    x ∈ intWin p L (L + len - 1) := by
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨L + i, by omega, by omega, rfl⟩

lemma stWin_cs_cs (D : StagData s) : stWin D p D.cs D.cs = intWin p (-((stMv D p D.cs : ℤ) - 1)) 0 := by
  simp [stWin, stagWin]

lemma stWin_c_cs (D : StagData s) {c : Fin s} (hc : c ≠ D.cs) :
    stWin D p c D.cs = intWin p (-(stB D.eCS p : ℤ)) (stB D.eCS p) := by
  simp [stWin, stagWin, hc]

lemma stWin_i_i (D : StagData s) {i : Fin s} (hi : i ≠ D.cs) :
    stWin D p i i = intWin p (-((stA D p : ℤ) + stMv D p i - 1)) (-(stA D p : ℤ)) := by
  simp [stWin, stagWin, hi]

lemma stWin_cs_i (D : StagData s) {i : Fin s} (hi : i ≠ D.cs) :
    stWin D p D.cs i = intWin p (halfZ p - stB D.eSC p) (halfZ p + stB D.eSC p) := by
  simp [stWin, stagWin, hi, Ne.symm hi]

lemma stWin_c_i (D : StagData s) {c i : Fin s} (hc : c ≠ D.cs) (hi : i ≠ D.cs) (hci : c ≠ i) :
    stWin D p c i = intWin p (-(stB D.eCC p : ℤ)) (stB D.eCC p) := by
  simp [stWin, stagWin, hi, hci, hc]

/-- Common consequences of `𝒫(p)` at a prime `p`. -/
structure P0Facts (D : StagData s) (p : ℕ) : Prop where
  hp0 : (0 : ℝ) < p
  hp7 : 7 < p
  hu : 2 < (D.u : ℝ) * p
  hT : 1 ≤ stT D.u p ∧ stT D.u p % 2 = 1 ∧ (stT D.u p : ℝ) ≤ D.u * p ∧ (D.u : ℝ) * p - 2 < stT D.u p
  heCS : 0 < D.eCS
  heSC : 0 < D.eSC
  heCC : 3 ≤ s → 0 < D.eCC
  hBcs : (D.eCS : ℝ) * p - 1 < stB D.eCS p ∧ (stB D.eCS p : ℝ) ≤ D.eCS * p
  hBsc : (D.eSC : ℝ) * p - 1 < stB D.eSC p ∧ (stB D.eSC p : ℝ) ≤ D.eSC * p
  hBcc : (D.eCC : ℝ) * p - 1 < stB D.eCC p ∧ (((s - 2 : ℕ) : ℝ) * stB D.eCC p ≤ ((s - 2 : ℕ) : ℝ) * D.eCC * p)
  hBcc' : 3 ≤ s → (stB D.eCC p : ℝ) ≤ D.eCC * p

lemma P0_facts (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ)) : P0Facts D p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨heCS, heSC, heCC⟩ := StP_eps D hs hv hp0 hP
  have hBcc' : 3 ≤ s → (stB D.eCC p : ℝ) ≤ D.eCC * p := fun h => (stB_facts D.eCC p).2 (heCC h).le
  have hp7 : 7 < p := by
    have h2 := stNP_ge_two D hp0 hP.1 D.cs (s - 2)
    have h6 := hP.2.2.2.2.2.2.2.1
    unfold stMstP at h6
    have : (0 : ℝ) ≤ D.eSC * p := by positivity
    have : (7 : ℝ) < p := by linarith
    exact_mod_cast this
  refine ⟨hp0, hp7, hP.1, stT_facts D.u p hP.1, heCS, heSC, heCC, ⟨(stB_facts _ p).1, (stB_facts _ p).2 heCS.le⟩,
    ⟨(stB_facts _ p).1, (stB_facts _ p).2 heSC.le⟩, ⟨(stB_facts _ p).1, ?_⟩, hBcc'⟩
  by_cases h3 : 3 ≤ s
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hBcc' h3) (Nat.cast_nonneg _)
  · have : s - 2 = 0 := by omega
    simp [this]

lemma stNu_eq (D : StagData s) (c' : Fin s) (t : ℕ) :
    (stNu D p c' t : ℝ) = stT D.u p * (stCoef D c' (D.rows c' t) : ℝ) := by
  unfold stNu; push_cast; ring

lemma stNu_ge (D : StagData s) (hv : D.Valid) (F : P0Facts D p) (c' : Fin s) {t : ℕ} (ht : t < s - 1) :
    stNuM D (p : ℝ) c' t < stNu D p c' t ∧ (stNu D p c' t : ℝ) ≤ stNuP D (p : ℝ) c' t ∧
      0 < stNuM D (p : ℝ) c' t ∧ 1 ≤ stNu D p c' t := by
  have hc := valid_coef D hv c' ht
  have hcR : (1 : ℝ) ≤ stCoef D c' (D.rows c' t) := by exact_mod_cast hc
  obtain ⟨hT1, -, hTle, hTgt⟩ := F.hT
  have hu := F.hu
  rw [stNu_eq]
  unfold stNuM stNuP
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_⟩
  unfold stNu; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

lemma stLen_ge (D : StagData s) (c' : Fin s) (t : ℕ) : stEll D (p : ℝ) c' t ≤ stLen D p c' t := by
  unfold stEll stLen stBr
  have := (stB_facts (stFrac D c' (D.rows c' t)) p).1
  push_cast; linarith

/-- `N_t ≤ N_t^+` (the substitutions `T > up - 2`, `|I| ≥ 2εp - 1`, `⌈z⌉ ≤ z + 1`). -/
lemma wsN_le_NP (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (F : P0Facts D p) (c' : Fin s) :
    ∀ t, t ≤ s - 2 → (wsN p (stLen D p c') (stNu D p c') t : ℝ) ≤ stNP D (p : ℝ) c' t := by
  have hs1 : ∀ t, t ≤ s - 2 → t < s - 1 := fun t ht => by omega
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨hlt, -, hpos, hν1⟩ := stNu_ge D hv F c' (hs1 0 (Nat.zero_le _))
    simp only [wsN, stNP]
    have hc := cdiv_le_add_one (p - stLen D p c' 0) (stNu D p c' 0) hν1
    have hνR : (0 : ℝ) < stNu D p c' 0 := by linarith
    push_cast
    have hm : ((p - stLen D p c' 0 : ℕ) : ℝ) / stNu D p c' 0 ≤
        max 0 (((p : ℝ) - stEll D (p : ℝ) c' 0) / stNuM D (p : ℝ) c' 0) := by
      by_cases hle : stLen D p c' 0 ≤ p
      · rw [Nat.cast_sub hle]
        have hl := stLen_ge (p := p) D c' 0
        refine le_trans ?_ (le_max_right _ _)
        exact div_le_div₀ (by linarith [show (stLen D p c' 0 : ℝ) ≤ p by exact_mod_cast hle]) (by linarith)
          hpos hlt.le
      · rw [show p - stLen D p c' 0 = 0 by omega]; simp
    linarith
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    obtain ⟨hlt, -, hpos, hν1⟩ := stNu_ge D hv F c' (hs1 (t + 1) ht)
    simp only [wsN, stNP]
    have hpos1 : 1 ≤ wsN p (stLen D p c') (stNu D p c') t :=
      wsN_pos p (Fact.out : p.Prime).one_lt.le _ _ t fun t' _ h2 =>
        (stNu_ge D hv F c' (hs1 t' (by omega))).2.2.2
    have hc := cdiv_le_add_one p (stNu D p c' (t + 1)) hν1
    have hdiv : (p : ℝ) / stNu D p c' (t + 1) ≤ p / stNuM D (p : ℝ) c' (t + 1) :=
      div_le_div_of_nonneg_left F.hp0.le hpos hlt.le
    rw [Nat.cast_add, Nat.cast_sub hpos1]
    push_cast
    linarith

lemma stNP_nonneg (D : StagData s) (F : P0Facts D p) (c' : Fin s) (t : ℕ) :
    0 ≤ stNP D (p : ℝ) c' t := by
  have := stNP_ge_two D F.hp0 F.hu c' t; linarith

/-- The row half-widths are below `p/2`. -/
lemma len_le_p (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ)) (F : P0Facts D p)
    (c' : Fin s) {t : ℕ} (ht : t < s - 1) : stLen D p c' t ≤ p := by
  have hMst2 := stNP_ge_two D F.hp0 F.hu D.cs (s - 2)
  obtain ⟨-, -, -, -, -, -, hP6a, hP6b, -⟩ := hP
  have hMP0 := stMP_nonneg D (p : ℝ)
  have hCS : (0 : ℝ) ≤ D.eCS * p := by have := F.heCS; positivity
  unfold stMstP at hP6b
  have hsCC : (0 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) * D.eCC * p := by
    by_cases h3 : 3 ≤ s
    · have := F.heCC h3; positivity
    · have : s - 2 = 0 := by omega
      simp [this]
  have key : ∀ B : ℕ, ((2 * B + 1 : ℕ) : ℝ) ≤ p → 2 * B + 1 ≤ p := fun B h => by exact_mod_cast h
  unfold stLen stBr
  apply key
  push_cast
  by_cases hc' : c' = D.cs
  · rw [hc', stFrac_cs]
    have := F.hBcs.2
    have : (2 * (s - 2 : ℕ) * D.eCC : ℝ) * p = 2 * (((s - 2 : ℕ) : ℝ) * D.eCC * p) := by ring
    nlinarith
  · rw [stFrac_i D hc']
    split_ifs with hr
    · have := F.hBsc.2; nlinarith
    · have h3 : 3 ≤ s := three_le_of (hv.1 c' t ht) hr hc'
      have := F.hBcc' h3
      have heCC := F.heCC h3
      have hs3 : (1 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ s - 2 by omega)
      have : (D.eCC : ℝ) * p ≤ ((s - 2 : ℕ) : ℝ) * D.eCC * p := by
        have : (0 : ℝ) ≤ D.eCC * p := by positivity
        nlinarith
      have h4 : (2 * (s - 2 : ℕ) * D.eCC : ℝ) * p = 2 * (((s - 2 : ℕ) : ℝ) * D.eCC * p) := by ring
      nlinarith

lemma stWin_cross (D : StagData s) {c c' : Fin s} (hc : c ≠ D.cs) (hcc : c ≠ c') :
    stWin D p c c' = intWin p (-(stB (stFrac D c' c) p : ℤ)) (stB (stFrac D c' c) p) := by
  by_cases h : c' = D.cs
  · rw [h, stWin_c_cs D hc, stFrac_cs]
  · rw [stWin_c_i D hc h hcc, stFrac_i D h, if_neg hc]

lemma two_ne_zero_p (hp : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- **`prop:P0`(a), condition (i)** of `prop:steer`: every depth-zero cross lies in its window (the crosses
`T n_{cc'}` within `[-B, B]` by (P3), the half-cell offsets `½ - (T n + 1)/2` within `½ + [-B_{⋆←C}, B_{⋆←C}]`). -/
theorem P0_cond_i (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ))
    (θ : ZMod p) (lamv : Fin s → ZMod p) (zθ : Fin s → PowerSeries (ZMod p))
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    ∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ stWin D p c c' := by
  have F := P0_facts D hs hv hP
  obtain ⟨hT1, hTodd, hTle, hTgt⟩ := F.hT
  have hu := F.hu
  have hp7 := F.hp7
  intro c c' hcc
  by_cases hc : c = D.cs
  · rw [hc] at hcc ⊢
    have hi : c' ≠ D.cs := Ne.symm hcc
    rw [stWin_cs_i D hi]
    have hmodd : D.nI D.cs c' % 2 = 1 := hv.2.2.2 c' hi
    have hTm : ((stT D.u p : ℤ) * D.nI D.cs c') % 2 = 1 := by
      have h1 : Odd (stT D.u p : ℤ) := by rw [Int.odd_iff]; omega
      exact Int.odd_iff.mp (h1.mul (Int.odd_iff.mpr hmodd))
    have h3 := hP.2.2.2.1 c' hi
    have hm1 : (1 : ℝ) ≤ ((D.nI D.cs c').natAbs : ℝ) := by
      exact_mod_cast Int.natAbs_pos.mpr (hv.2.2.1 _ _ hcc)
    have hTm_le : ((stT D.u p : ℤ) * D.nI D.cs c').natAbs + 1 < 2 * stB D.eSC p := by
      have hR : ((((stT D.u p : ℤ) * D.nI D.cs c').natAbs : ℕ) : ℝ) =
          (stT D.u p : ℝ) * ((D.nI D.cs c').natAbs : ℝ) := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]; push_cast; ring
      have hB := F.hBsc.1
      have : ((((stT D.u p : ℤ) * D.nI D.cs c').natAbs : ℕ) : ℝ) + 1 < 2 * (stB D.eSC p : ℝ) := by
        rw [hR]
        have : (stT D.u p : ℝ) * ((D.nI D.cs c').natAbs : ℝ) ≤ ((D.nI D.cs c').natAbs : ℝ) * ((D.u : ℝ) * p) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hTle (by positivity)
        linarith
      exact_mod_cast this
    have hz1 : -((stB D.eSC p : ℤ)) ≤ -(((stT D.u p : ℤ) * D.nI D.cs c' + 1) / 2) ∧
        -(((stT D.u p : ℤ) * D.nI D.cs c' + 1) / 2) ≤ (stB D.eSC p : ℤ) := by
      have := hTm_le
      constructor <;> omega
    refine ⟨halfZ p - ((stT D.u p : ℤ) * D.nI D.cs c' + 1) / 2, by omega, by omega, ?_⟩
    have h2h := halfZ_two p (by omega)
    have h2z : 2 * (halfZ p - ((stT D.u p : ℤ) * D.nI D.cs c' + 1) / 2) =
        (p : ℤ) - (stT D.u p : ℤ) * D.nI D.cs c' := by omega
    have hc2 := congrArg (fun z : ℤ => (z : ZMod p)) h2z
    push_cast at hc2
    rw [ZMod.natCast_self, zero_sub] at hc2
    have hk := hκh c' hi
    push_cast at hk
    apply mul_left_cancel₀ (two_ne_zero_p (p := p) (by omega))
    push_cast
    rw [hc2, ← hk]
    exact (mul_neg _ _).symm
  · rw [stWin_cross D hc hcc, hκ c c' hc hcc]
    have h3 := hP.2.2.1 c c' hc hcc
    have hB := (stB_facts (stFrac D c' c) p).1
    have hle : (stT D.u p : ℝ) * ((D.nI c c').natAbs : ℝ) < stB (stFrac D c' c) p := by
      have : (stT D.u p : ℝ) * ((D.nI c c').natAbs : ℝ) ≤ ((D.nI c c').natAbs : ℝ) * ((D.u : ℝ) * p) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hTle (by positivity)
      linarith
    have hle' : ((stT D.u p : ℤ) * D.nI c c').natAbs ≤ stB (stFrac D c' c) p := by
      have : ((((stT D.u p : ℤ) * D.nI c c').natAbs : ℕ) : ℝ) < stB (stFrac D c' c) p := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]; push_cast; exact hle
      exact_mod_cast this.le
    refine ⟨-((stT D.u p : ℤ) * D.nI c c'), by omega, by omega, Int.cast_neg _⟩

lemma stLen_cs (D : StagData s) (t : ℕ) : stLen D p D.cs t = 2 * stB D.eCS p + 1 := by
  simp [stLen, stBr, stFrac_cs]

lemma stLen_i (D : StagData s) {i : Fin s} (hi : i ≠ D.cs) (t : ℕ) :
    stLen D p i t = 2 * stB (if D.rows i t = D.cs then D.eSC else D.eCC) p + 1 := by
  simp [stLen, stBr, stFrac_i D hi]

/-- The hypotheses of `lem:ws` for every column (from (P2): `ν_1^+ ≤ ℓ_1`, `N^+_{t-1} ν_t^+ ≤ ℓ_t`). -/
lemma P0_ws (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ)) (F : P0Facts D p)
    (c' : Fin s) :
    stNu D p c' 0 ≤ stLen D p c' 0 ∧
      ∀ t, t + 1 < s - 1 → wsN p (stLen D p c') (stNu D p c') t * stNu D p c' (t + 1) ≤ stLen D p c' (t + 1) := by
  constructor
  · have h := (hP.2.1 c').1
    have h1 := (stNu_ge D hv F c' (show 0 < s - 1 by omega)).2.1
    have h2 := stLen_ge (p := p) D c' 0
    have : (stNu D p c' 0 : ℝ) ≤ stLen D p c' 0 := by linarith
    exact_mod_cast this
  · intro t ht
    have h := (hP.2.1 c').2 t (by omega)
    have h1 := stNu_ge D hv F c' (show t + 1 < s - 1 from ht)
    have h2 := stLen_ge (p := p) D c' (t + 1)
    have h3 := wsN_le_NP D hs hv F c' t (by omega)
    have h0 : (0 : ℝ) ≤ stNu D p c' (t + 1) := Nat.cast_nonneg _
    have hW0 : (0 : ℝ) ≤ wsN p (stLen D p c') (stNu D p c') t := Nat.cast_nonneg _
    have hNP0 := stNP_nonneg D F c' t
    have : ((wsN p (stLen D p c') (stNu D p c') t * stNu D p c' (t + 1) : ℕ) : ℝ) ≤ stLen D p c' (t + 1) := by
      push_cast
      calc (wsN p (stLen D p c') (stNu D p c') t : ℝ) * stNu D p c' (t + 1)
          ≤ stNP D (p : ℝ) c' t * stNuP D (p : ℝ) c' (t + 1) := mul_le_mul h3 h1.2.1 h0 hNP0
        _ ≤ _ := h.trans h2
    exact_mod_cast this

/-- **`prop:P0`(a), condition (ii)** of `prop:steer`: column `c⋆` covers by `lem:ws`, every other column is a
doubled column (`lem:D`). -/
theorem P0_cond_ii (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ))
    (θ : ZMod p) (lamv : Fin s → ZMod p) (zθ : Fin s → PowerSeries (ZMod p))
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin (stWin D p) c') := by
  have F := P0_facts D hs hv hP
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  intro c'
  rw [cover_iff]
  intro σ
  obtain ⟨hws1, hwsN⟩ := P0_ws D hs hv hP F c'
  have hlen : ∀ t < s - 1, stLen D p c' t ≤ p := fun t ht => len_le_p D hs hv hP F c' ht
  have hν1 : ∀ t < s - 1, 1 ≤ stNu D p c' t := fun t ht => (stNu_ge D hv F c' ht).2.2.2
  have hNpos : 1 ≤ stN D p c' := by
    unfold stN
    exact wsN_pos p hp1 _ _ _ fun t' _ h2 => hν1 t' (by omega)
  by_cases hc' : c' = D.cs
  · -- column `c⋆`: `lem:ws`
    subst hc'
    set v : ℕ → ℤ := fun t => (stT D.u p : ℤ) * D.nI (D.rows D.cs t) D.cs with hvdef
    have hvabs : ∀ t, (v t).natAbs = stNu D p D.cs t := by
      intro t; simp [hvdef, stNu, stCoef, Int.natAbs_mul]
    have hfun : (fun t => (v t).natAbs) = stNu D p D.cs := funext hvabs
    obtain ⟨o, ho1, ho2, hgood⟩ := ws_cover p (s - 1) (by omega) v (fun _ => -(stB D.eCS p : ℤ))
      (stLen D p D.cs) hlen (fun t ht => by rw [hvabs]; exact hν1 t ht) (by rw [hvabs]; exact hws1)
      (fun t ht => by rw [hfun, hvabs]; exact hwsN t ht) (fun t => σ (D.rows D.cs t))
      (-((stMv D p D.cs : ℤ) - 1))
    rw [hfun] at ho2
    have hM : stMv D p D.cs = wsN p (stLen D p D.cs) (stNu D p D.cs) (s - 1 - 1) := by
      simp [stMv, stN]; rfl
    refine ⟨(o : ZMod p), ?_, fun c hc => ?_⟩
    · rw [stWin_cs_cs]
      refine ⟨o, ho1, ?_, rfl⟩
      have h2 := ho2; rw [hM] at h2; omega
    · obtain ⟨t, ht, hrow⟩ := valid_rows D hv hc
      have hg := hgood t ht
      simp only [hvdef, hrow] at hg
      rw [hκ c D.cs hc hc, stWin_c_cs D hc]
      have := arc_sub_intWin _ _ _ hg
      rw [stLen_cs] at this
      convert this using 2
      push_cast; ring
  · -- a doubled column: `lem:D`
    have hi := hc'
    set u : ℕ → ZMod p := fun t => kapL θ lamv zθ (D.rows c' t) c' with hudef
    set v : ℕ → ℤ := fun t => if D.rows c' t = D.cs then (stT D.u p : ℤ) * D.nI D.cs c'
      else 2 * ((stT D.u p : ℤ) * D.nI (D.rows c' t) c') with hvdef
    set L : ℕ → ℤ := fun t => if D.rows c' t = D.cs then halfZ p - stB D.eSC p else -(stB D.eCC p : ℤ)
      with hLdef
    have hvabs : ∀ t, (v t).natAbs = stNu D p c' t := by
      intro t
      simp only [hvdef, stNu, stCoef, hi, false_or]
      split_ifs with h
      · rw [h, Int.natAbs_mul, Int.natAbs_natCast]
      · rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]; simp; ring
    have hfun : (fun t => (v t).natAbs) = stNu D p c' := funext hvabs
    have hv2 : ∀ t < s - 1, (v t : ZMod p) = 2 * u t := by
      intro t ht
      simp only [hvdef, hudef]
      split_ifs with h
      · rw [h, hκh c' hi]
      · rw [hκ (D.rows c' t) c' h (hv.1 c' t ht)]; push_cast; ring
    obtain ⟨o, ho1, ho2, hgood⟩ := lemD p (s - 1) (by omega) u v hv2 L (stLen D p c') hlen
      (fun t ht => by rw [hvabs]; exact hν1 t ht) (by rw [hvabs]; exact hws1)
      (fun t ht => by rw [hfun, hvabs]; exact hwsN t ht) (fun t => σ (D.rows c' t))
      (-((stA D p : ℤ) + stMv D p c' - 1))
    rw [hfun] at ho2
    have hM : stMv D p c' = 2 * wsN p (stLen D p c') (stNu D p c') (s - 1 - 1) - 1 := by
      simp [stMv, stN, hi]; rfl
    have hN1 : 1 ≤ wsN p (stLen D p c') (stNu D p c') (s - 1 - 1) := by
      have := hNpos; unfold stN at this; rwa [show s - 2 = s - 1 - 1 by omega] at this
    refine ⟨(o : ZMod p), ?_, fun c hc => ?_⟩
    · rw [stWin_i_i D hi]
      refine ⟨o, ho1, ?_, rfl⟩
      have hcast : ((stMv D p c' : ℕ) : ℤ) = 2 * (wsN p (stLen D p c') (stNu D p c') (s - 1 - 1) : ℤ) - 1 := by
        rw [hM]; omega
      omega
    · obtain ⟨t, ht, hrow⟩ := valid_rows D hv hc
      have hg := hgood t ht
      have harc := arc_sub_intWin _ _ _ hg
      simp only [hudef, hLdef, hrow] at harc
      rw [stLen_i D hi, hrow] at harc
      by_cases hcs : c = D.cs
      · rw [hcs] at harc ⊢
        simp only [if_true] at harc
        rw [stWin_cs_i D hi]
        convert harc using 2
        push_cast; ring
      · simp only [if_neg hcs] at harc
        rw [stWin_c_i D hcs hi hc]
        convert harc using 2
        push_cast; ring

lemma stMv_cs_le (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (F : P0Facts D p) :
    (stMv D p D.cs : ℝ) ≤ stMstP D (p : ℝ) := by
  have := wsN_le_NP D hs hv F D.cs (s - 2) le_rfl
  simp only [stMv, if_true, stN]; exact this

lemma stMv_i_le (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (F : P0Facts D p) {i : Fin s}
    (hi : i ≠ D.cs) : (stMv D p i : ℝ) ≤ stMP D (p : ℝ) := by
  have h1 := wsN_le_NP D hs hv F i (s - 2) le_rfl
  have h2 := stMP_ge D (p : ℝ) i hi
  have hN : 1 ≤ stN D p i := wsN_pos p (Fact.out : p.Prime).one_lt.le _ _ _ fun t' _ h2 =>
    (stNu_ge D hv F i (show t' < s - 1 by omega)).2.2.2
  simp only [stMv, hi, if_false]
  rw [Nat.cast_sub (by omega)]
  push_cast
  unfold stN at hN ⊢
  linarith

lemma stM_le (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (F : P0Facts D p) :
    (stM D p : ℝ) ≤ stMP D (p : ℝ) := by
  obtain ⟨c, hc⟩ := exists_ne_cs D.cs hs
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (univ.erase D.cs) ⟨c, mem_erase.mpr ⟨hc, mem_univ _⟩⟩
    (stMv D p)
  unfold stM; rw [heq]
  exact stMv_i_le D hs hv F (ne_of_mem_erase hi)

/-- **`prop:P0`(a), the window bound**: the staggered rule satisfies the hypotheses of `lem:W` (`M_i, M⋆ ≥ 1`,
`M = max M_i`, (D) with equality, (N)) and the three inequalities of its last statement, with
`M⋆ ≤ M⋆^+(p)`. -/
theorem P0_W (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ)) :
    (∀ c, 1 ≤ stMv D p c) ∧ (∀ i, i ≠ D.cs → stMv D p i ≤ stM D p) ∧
    stA D p = (s - 2) * stB D.eCC p + stB D.eCS p ∧
    stA D p + stM D p + (s - 2) * stB D.eCC p + stB D.eCS p ≤ p ∧
    2 * stB D.eSC p + 2 * stMv D p D.cs ≤ p - 3 ∧
    (stM D p : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p ∧
    2 * (1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) * stM D p +
        2 * (1 / 2 - (stB D.eSC p : ℝ) / p) * (stMv D p D.cs + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) ^ 2 +
        (1 / 2 - (stB D.eSC p : ℝ) / p) ^ 2 - 1) ∧
    1 / Real.sqrt 2 ≤ 1 - (2 * (stA D p : ℝ) + stM D p) / p ∧
    (stMv D p D.cs : ℝ) ≤ stMstP D (p : ℝ) := by
  have F := P0_facts D hs hv hP
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hp0 := F.hp0
  have hMst := stMv_cs_le D hs hv F
  have hM := stM_le D hs hv F
  have hMP0 := stMP_nonneg D (p : ℝ)
  have hMst2 := stNP_ge_two D hp0 F.hu D.cs (s - 2)
  obtain ⟨-, -, -, -, ⟨hP4a, hP4b⟩, ⟨hP5a, hP5b⟩, hP6a, hP6b, hP6c⟩ := hP
  unfold stMstP at hP6b hP4b hMst
  unfold stZ at hP5a hP5b
  have hBcs := F.hBcs.2
  have hBsc := F.hBsc.2
  have hBcc := F.hBcc.2
  have hν1 : ∀ c' : Fin s, ∀ t < s - 1, 1 ≤ stNu D p c' t := fun c' t ht => (stNu_ge D hv F c' ht).2.2.2
  have hNpos : ∀ c', 1 ≤ stN D p c' := fun c' =>
    wsN_pos p hp1 _ _ _ fun t' _ h2 => hν1 c' t' (by omega)
  have hA : (stA D p : ℝ) = ((s - 2 : ℕ) : ℝ) * stB D.eCC p + stB D.eCS p := by
    unfold stA; push_cast; ring
  -- `x`, `y` (real, from the design) and their integer versions
  have hX : (stX D : ℝ) = 1 - ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS := by unfold stX; push_cast; ring
  have hY : (stY D : ℝ) = 1 / 2 - D.eSC := by unfold stY; push_cast; ring
  set xi := 1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p with hxi
  set yi := 1 / 2 - (stB D.eSC p : ℝ) / p with hyi
  have hxx : (stX D : ℝ) ≤ xi := by
    rw [hX, hxi]
    have : (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p ≤ ((s - 2 : ℕ) : ℝ) * D.eCC + 2 * D.eCS := by
      rw [div_le_iff₀ hp0]; nlinarith
    linarith
  have hyy : (stY D : ℝ) ≤ yi := by
    rw [hY, hyi]
    have : (stB D.eSC p : ℝ) / p ≤ D.eSC := by rw [div_le_iff₀ hp0]; linarith
    linarith
  have hMdiv : (stM D p : ℝ) / p ≤ stMP D (p : ℝ) / p := div_le_div_of_nonneg_right hM hp0.le
  refine ⟨fun c => ?_, fun i hi => Finset.le_sup (mem_erase.mpr ⟨hi, mem_univ _⟩), rfl, ?_, ?_, ?_, ?_, ?_,
    hMst⟩
  · unfold stMv; split_ifs
    · exact hNpos c
    · have := hNpos c; omega
  · -- (N), first part
    have : ((stA D p + stM D p + (s - 2) * stB D.eCC p + stB D.eCS p : ℕ) : ℝ) ≤ p := by
      push_cast
      rw [hA]
      linarith
    exact_mod_cast this
  · -- (N), second part
    have : ((2 * stB D.eSC p + 2 * stMv D p D.cs : ℕ) : ℝ) + 3 ≤ p := by
      push_cast; linarith
    have : 2 * stB D.eSC p + 2 * stMv D p D.cs + 3 ≤ p := by exact_mod_cast this
    omega
  · -- `x ≥ M/p`
    linarith
  · -- `p(x² + y² - 1) ≥ 2xM + 2y(M⋆ + ½)`
    have hx0 : 0 ≤ (stX D : ℝ) := le_trans (div_nonneg hMP0 hp0.le) hP6c.le
    have hpx : stMP D (p : ℝ) ≤ p * stX D := by
      have := hP6c; rw [div_lt_iff₀ hp0] at this; linarith
    have hySC : (stNP D (p : ℝ) D.cs (s - 2)) + 3 / 2 ≤ p * stY D := by rw [hY]; linarith
    have hy0 : 0 ≤ (stY D : ℝ) :=
      (coef_pos_of (stY D : ℝ) (p : ℝ) (stNP D (p : ℝ) D.cs (s - 2) + 3 / 2) hp0 (by linarith)
        (by linarith)).le
    have e1 : (p : ℝ) * stX D ≤ p * xi := mul_le_mul_of_nonneg_left hxx hp0.le
    have e2 : (p : ℝ) * stY D ≤ p * yi := mul_le_mul_of_nonneg_left hyy hp0.le
    have h1 : 0 ≤ (xi - stX D) * (p * (xi + stX D) - 2 * stM D p) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (yi - stY D) * (p * (yi + stY D) - 2 * (stMv D p D.cs + 1 / 2)) :=
      mul_nonneg (by linarith) (by linarith)
    have h3 : 2 * (stX D : ℝ) * stM D p ≤ 2 * stX D * stMP D (p : ℝ) :=
      mul_le_mul_of_nonneg_left hM (by linarith)
    have h4 : 2 * (stY D : ℝ) * (stMv D p D.cs + 1 / 2) ≤ 2 * stY D * (stNP D (p : ℝ) D.cs (s - 2) + 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linear_combination hP4b + h1 + h2 + h3 + h4
  · -- `1 - (2A + M)/p ≥ 1/√2`
    set z := 1 - 2 * ((s - 2 : ℕ) : ℝ) * (D.eCC : ℝ) - 2 * (D.eCS : ℝ) - stMP D (p : ℝ) / p
    have hzle : z ≤ 1 - (2 * (stA D p : ℝ) + stM D p) / p := by
      have : (2 * (stA D p : ℝ) + stM D p) / p ≤ 2 * ((s - 2 : ℕ) : ℝ) * D.eCC + 2 * D.eCS + stMP D (p : ℝ) / p := by
        rw [div_le_iff₀ hp0, hA, add_mul, div_mul_cancel₀ _ hp0.ne']
        linarith
      linarith
    have hsq : 1 / Real.sqrt 2 ≤ z := by
      have h0 : 0 ≤ 1 / Real.sqrt 2 := by positivity
      have h12 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      rw [← pow_le_pow_iff_left₀ h0 hP5a (by norm_num : (2 : ℕ) ≠ 0), h12]
      linarith
    linarith

/-- **`prop:P0`(a)**: at every prime `p` with `𝒫(p)`, if the crosses of the frame are `κ_{c←c'} = T n_{cc'}`
(`c ≠ c⋆`) and `2κ_{⋆←i} = T L/Q_i` (as `lem:R` gives), the staggered rule satisfies (i) and (ii) of
`prop:steer` and the hypotheses of `lem:W` including its last statement, with `M⋆ ≤ M⋆^+(p)`. -/
theorem P0_a (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ))
    (θ : ZMod p) (lamv : Fin s → ZMod p) (zθ : Fin s → PowerSeries (ZMod p))
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    (∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ stWin D p c c') ∧
    (∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin (stWin D p) c')) ∧
    (∀ c, 1 ≤ stMv D p c) ∧ (∀ i, i ≠ D.cs → stMv D p i ≤ stM D p) ∧
    stA D p = (s - 2) * stB D.eCC p + stB D.eCS p ∧
    stA D p + stM D p + (s - 2) * stB D.eCC p + stB D.eCS p ≤ p ∧
    2 * stB D.eSC p + 2 * stMv D p D.cs ≤ p - 3 ∧
    (stM D p : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p ∧
    2 * (1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) * stM D p +
        2 * (1 / 2 - (stB D.eSC p : ℝ) / p) * (stMv D p D.cs + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) ^ 2 +
        (1 / 2 - (stB D.eSC p : ℝ) / p) ^ 2 - 1) ∧
    1 / Real.sqrt 2 ≤ 1 - (2 * (stA D p : ℝ) + stM D p) / p ∧
    (stMv D p D.cs : ℝ) ≤ stMstP D (p : ℝ) :=
  ⟨P0_cond_i D hs hv hP θ lamv zθ hκ hκh, P0_cond_ii D hs hv hP θ lamv zθ hκ hκh, P0_W D hs hv hP⟩

end Prime




section Seq

variable {s : ℕ}

lemma sepAtLevel_le {q s K : ℕ} {pt : ℕ → Fin s → ℝ} {a b : ℝ} (h : SepAtLevel q s K pt a) (hba : b ≤ a) :
    SepAtLevel q s K pt b :=
  fun v w hv hw hvw => hba.trans (h v w hv hw hvw)

/-- **`prop:P0`, consequence** (with `P0_mono`): if `𝒫(p₀)` holds (`p₀ > 0` real), then for every prime
`p ≥ p₀` and every frame with the crosses `κ_{c←c'} = T n_{cc'}`, `2κ_{⋆←i} = T L/Q_i` (constants `λ_c ≠ 0`,
scale `θ ≠ 0`, local roots of a monic `w` of degree `s` with distinct places), selection rules for the
staggered rule exist, and every selection rule gives a quasi-uniform digital `(0,s)`-sequence over `𝔽_p` with
`c(P_{sK}) ≥ 1 - M⋆/p ≥ 1 - C''/p` for every `K ≥ 1`, `C'' = M⋆^+(p₀)` (and `M⋆ ≤ C''`, `M⋆` the integer own
size of column `c⋆`). -/
theorem P0_seq (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (p0 : ℝ) (hp0 : 0 < p0) (hP0 : StP D p0)
    (p : ℕ) [Fact p.Prime] (hpp : p0 ≤ p) (w : (ZMod p)[X]) (hw : w.Monic) (hdeg : w.natDegree = s)
    (θ : ZMod p) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (lamv : Fin s → ZMod p) (hlam : ∀ c, lamv c ≠ 0)
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    (stMv D p D.cs : ℝ) ≤ stMstP D p0 ∧
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (stWin D p) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (stWin D p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))
        (1 - (stMv D p D.cs : ℝ) / p)) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))
        (1 - stMstP D p0 / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))) ≤
          Real.sqrt s * p / (1 - stMstP D p0 / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ)))) := by
  obtain ⟨hP, hMmono⟩ := P0_mono D hp0 hpp hP0
  have F := P0_facts D hs hv hP
  obtain ⟨hi, hii, hM1, hM, hA, hN1, hN2, hx, hxy, hz, hMst⟩ := P0_a D hs hv hP θ lamv zθ hκ hκh
  have hMst0 : (stMv D p D.cs : ℝ) ≤ stMstP D p0 := hMst.trans hMmono
  have hp5 : 5 ≤ p := by have := F.hp7; omega
  have hpR := F.hp0
  have hLB : WinLB p (stWin D p) (1 - (stMv D p D.cs : ℝ) / p) :=
    lemW_lb hs D.cs (stA D p) (stMv D p) (stM D p) (stB D.eCC p) (stB D.eSC p) (stB D.eCS p) hM1 hM hA hN1
      hN2 hx hxy hz
  obtain ⟨-, ⟨rule, hrule⟩, hall⟩ := steer p hp5 w hw hdeg θ hθ zθ hroot hinj lamv hlam (stWin D p) hi hii
  -- `M⋆^+(p₀) < p₀/2`
  have hC : stMstP D p0 / p < 1 / 2 := by
    obtain ⟨-, heSC, -⟩ := StP_eps D hs hv hp0 hP0
    have h6 := hP0.2.2.2.2.2.2.2.1
    unfold stMstP at h6 ⊢
    have : (0 : ℝ) ≤ (D.eSC : ℝ) * p0 := by positivity
    rw [div_lt_iff₀ hpR]; linarith
  have hLBpos : 0 < 1 - stMstP D p0 / p := by linarith
  have hle1 : 1 - (stMv D p D.cs : ℝ) / p ≤ 1 := by
    have : (0 : ℝ) ≤ (stMv D p D.cs : ℝ) / p := by positivity
    linarith
  have hmono : 1 - stMstP D p0 / p ≤ 1 - (stMv D p D.cs : ℝ) / p := by
    have := div_le_div_of_nonneg_right hMst0 hpR.le; linarith
  refine ⟨hMst0, ⟨rule, hrule⟩, fun rule' hrule' => ?_⟩
  obtain ⟨-, hseq, -, hcert⟩ := hall rule' hrule'
  have hsep : ∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule') zθ))
      (1 - (stMv D p D.cs : ℝ) / p) := by
    intro K hK
    have := (hcert _ hLB K hK).2
    rwa [min_eq_right hle1] at this
  have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule') zθ))
      (1 - stMstP D p0 / p) := fun K hK => sepAtLevel_le (hsep K hK) hmono
  exact ⟨hseq, hsep, hsep', fun N hN => prefix_mesh (zcode p) _ (by omega) (by omega) hseq _ hLBpos hsep' N hN⟩

/-- **The staggered rule of a staggered design** (`def:BS`, `lem:R`, `prop:P0`): let `D` be a staggered design over
an integer frame with `δ`, `L` as in `lem:R` (`sdLOK`), rows/fractions/`u` with valid data, and `𝒫(p₀)`. For
every prime `p ≥ p₀` as in `lem:R` (dividing none of the `a_c - a_{c'}`, the numerators and denominators of
the `Q_j`, `L` and `T`), with `θ = 2^δ L T`, the constants `λ_c = g_c w'(a_c)` of `lem:R` and the windows of the
rule, selection rules exist and every selection rule gives a quasi-uniform digital `(0,s)`-sequence with
`c(P_{sK}) ≥ 1 - M⋆/p ≥ 1 - M⋆^+(p₀)/p` for every `K ≥ 1`; the same holds for every multiplier family with
these constants and all responses in the windows ("every selection rule", `prop:steer`). -/
theorem P0_design (D : StagDesign s) (hs : 2 ≤ s) (hD : sdOK D) (δ L : ℕ) (hL : sdLOK D δ L)
    (rows : Fin s → ℕ → Fin s) (eCS eCC eSC u : ℚ)
    (hv : (sdData D δ L rows eCS eCC eSC u).Valid)
    (p0 : ℝ) (hp0 : 0 < p0) (hP0 : StP (sdData D δ L rows eCS eCC eSC u) p0)
    (p : ℕ) [Fact p.Prime] (hpp : p0 ≤ p)
    (hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0)
    (hpQ : ∀ j, j ≠ D.cs → ((D.Q j).num : ZMod p) ≠ 0 ∧ ((D.Q j).den : ZMod p) ≠ 0)
    (hpL : (L : ZMod p) ≠ 0) (hpT : (stT u p : ZMod p) ≠ 0)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) :
    (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) ≤ stMstP (sdData D δ L rows eCS eCC eSC u) p0 ∧
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows eCS eCC eSC u) p) rule) ∧
    (∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows eCS eCC eSC u) p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
        (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
        (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))) ≤
          Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
              (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))))) ∧
    ∀ g : Fin s → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam D p δ c) →
      RespInS (ssGen g zθ) (stWin (sdData D δ L rows eCS eCC eSC u) p) →
      IsSeq0 (zcode p) (ssGen g zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
        (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
        (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
          Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  set SD := sdData D δ L rows eCS eCC eSC u with hSD
  have hu : SD.u = u := rfl
  obtain ⟨hP, -⟩ := P0_mono SD hp0 hpp hP0
  have F := P0_facts SD hs hv hP
  have hp2 : p ≠ 2 := by have := F.hp7; omega
  have hT := F.hT
  rw [hu] at hT
  obtain ⟨hθ, hlam, hκ, hκh⟩ := lemR_Fp hp2 D hD δ L (stT u p) hL hT.2.1 hpa hpQ hpL hpT zθ hplace
  have hinj : Function.Injective (ssPlace zθ) := by
    intro b c h
    by_contra hne
    simp only [ssPlace, hplace] at h
    exact hpa b c hne (by push_cast; rw [h, sub_self])
  have hκ' : ∀ c c', c ≠ SD.cs → c ≠ c' → kapL (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ c c' =
      (((stT SD.u p : ℤ) * SD.nI c c' : ℤ) : ZMod p) := by
    intro c c' hc hcc
    have hc' : c ≠ D.cs := hc
    rw [hκ c c' hc' hcc]
    simp [hSD, sdData, hc']
  have hκh' : ∀ i, i ≠ SD.cs → 2 * kapL (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ SD.cs i =
      (((stT SD.u p : ℤ) * SD.nI SD.cs i : ℤ) : ZMod p) := by
    intro i hi
    have hi' : i ≠ D.cs := hi
    change 2 * kapL _ _ zθ D.cs i = _
    rw [(hκh i hi').1]
    simp [hSD, sdData]
  have hmain := P0_seq SD hs hv p0 hp0 hP0 p hpp (framePoly p s D.fr) (framePoly_monic p s D.fr)
    (framePoly_natDegree p s D.fr) _ hθ zθ hroot hinj _ hlam hκ' hκh'
  have hii := P0_cond_ii SD hs hv hP _ _ zθ hκ' hκh'
  refine ⟨hmain.1, hmain.2.1, hmain.2.2, fun g hg hlg hW => ?_⟩
  obtain ⟨rule, hrule, rfl⟩ := steer_every p (framePoly p s D.fr) (framePoly_monic p s D.fr)
    (framePoly_natDegree p s D.fr) _ hθ zθ hroot hinj _ (stWin SD p) hii g hg hlg hW
  exact hmain.2.2 rule hrule

end Seq

end GeoSeq
