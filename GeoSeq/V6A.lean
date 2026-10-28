/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V6P0c
public import GeoSeq.V5BS

@[expose] public section

/-!
# GeoSeq stage V6: `thm:A` (separation `1 - O(1/p)` in every dimension)

The proof of `thm:A`: Faure places `(0, …, s-1)`, staggered coordinate `0`, natural order of `C`,
`Q_r = R^r` with an odd integer `R` (`taDesign`), uniform window fractions `ε = 1/(10s) < ε_s`, rows of decreasing
exponent (`taRows`). By `lem:R` every step of column `c'` in row `c` is `L R^{c-c'}` times a factor `w(c,c')` that does
not depend on `R` (`stCoef_ta`); for `R` large consecutive steps of every column differ by a factor at least
`1 + 1/ε` (`coef_ratio`), and `u = ε/(2 S)` (`S` the sum of all steps divided by `T`) puts every step at most
`ε/2`; then the limit hierarchy holds (`hier_geom`, the geometric series of the paper), `prop:P0`(c) (`P0_c_nat`)
gives `p₀`, and `P0_design` the sequence.

* **`A`** (`thm:A`): for every `s ≥ 3` such a design, `δ`, `L` (the least values of `lem:R`), rational `ε`, `u` and a
  natural number `p₀` with `𝒫(p₀)` (an exact decidable statement, so `p₀(s)` is effectively computable) such that
  for every prime `p ≥ p₀` (no congruence condition) the staggered rule gives a quasi-uniform digital
  `(0,s)`-sequence with `c(P_{sK}) ≥ 1 - C''_s/p` for every `K ≥ 1`, `C''_s = M⋆^+(p₀)`.
-/

namespace GeoSeq

open Finset PowerSeries Filter
open scoped Polynomial

/-! ## The Faure frame and the design `taDesign` -/

lemma frameA_faure {s c : ℕ} (hc : c < s) : frameA (faureFr s) c = c := by
  simp [frameA, faureFr, hc]

lemma intCast_ne_zero_of_abs_lt {p : ℕ} [Fact p.Prime] (z : ℤ) (hz : z ≠ 0) (h : |z| < p) :
    (z : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  exact hz (Int.eq_zero_of_abs_lt_dvd h0 h)

section Design

variable {s : ℕ} [NeZero s]

lemma taDesign_Q (R : ℕ) (j : Fin s) : (taDesign s R).Q j = (R : ℚ) ^ (j : ℕ) := rfl

lemma taQ_num (R : ℕ) (j : Fin s) : ((taDesign s R).Q j).num = (R : ℤ) ^ (j : ℕ) := by
  rw [taDesign_Q, show ((R : ℚ) ^ (j : ℕ)) = (((R : ℤ) ^ (j : ℕ) : ℤ) : ℚ) by push_cast; ring, Rat.num_intCast]

lemma taQ_den (R : ℕ) (j : Fin s) : ((taDesign s R).Q j).den = 1 := by
  rw [taDesign_Q, show ((R : ℚ) ^ (j : ℕ)) = (((R : ℤ) ^ (j : ℕ) : ℤ) : ℚ) by push_cast; ring, Rat.den_intCast]

lemma taDesign_ok (R : ℕ) (hR : R % 2 = 1) : sdOK (taDesign s R) := by
  refine ⟨fun b c h => ?_, fun j _ => ⟨?_, ?_, ?_⟩⟩
  · show frameA (faureFr s) b ≠ frameA (faureFr s) c
    rw [frameA_faure b.2, frameA_faure c.2]
    exact_mod_cast Fin.val_ne_of_ne h
  · rw [taDesign_Q]; have : (0 : ℚ) < R := by exact_mod_cast (show 0 < R by omega)
    positivity
  · rw [taQ_num]
    have : Odd ((R : ℤ) ^ (j : ℕ)) := (Int.odd_iff.mpr (by exact_mod_cast hR)).pow
    exact Int.odd_iff.mp this
  · rw [taQ_den]

lemma sdDelta_ta (R R' : ℕ) (c c' : Fin s) : sdDelta (taDesign s R) c c' = sdDelta (taDesign s R') c c' := rfl

lemma taDesign_cs (R : ℕ) : (taDesign s R).cs = 0 := rfl

/-- **The exponents of `R`** (proof of `thm:A`): for `c ≠ c⋆ = 0`, `n_{cc'} R^{c'} = L R^c n°_{cc'}|_{R=1}`. -/
lemma sdN_ta (R : ℕ) (hR : 0 < R) (δ L : ℕ) {c c' : Fin s} (hc : c ≠ 0) :
    sdN (taDesign s R) δ L c c' * (R : ℚ) ^ (c' : ℕ) =
      L * (R : ℚ) ^ (c : ℕ) * sdN (taDesign s 1) δ 1 c c' := by
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold sdN
  simp only [taDesign_cs, if_neg hc, sdDelta_ta R 1, taDesign_Q, Nat.cast_one, one_pow]
  by_cases hc' : c' = 0
  · subst hc'; simp <;> ring
  · simp only [if_neg hc']
    have : (R : ℚ) ^ (c' : ℕ) ≠ 0 := pow_ne_zero _ hR0
    field_simp

lemma taG_ne (δ : ℕ) {c c' : Fin s} (h : c ≠ c') : taG s δ c c' ≠ 0 := by
  unfold taG
  split_ifs with hc
  · exact one_ne_zero
  have hD := taDesign_ok (s := s) 1 rfl
  have h1 : (sdDelta (taDesign s 1) c c' : ℚ) ≠ 0 := by exact_mod_cast sdDelta_ne _ hD h
  have h2 : (sdDelta (taDesign s 1) 0 c : ℚ) ≠ 0 := by exact_mod_cast sdDelta_ne _ hD (Ne.symm hc)
  have h1' : (sdDelta (taDesign s 1) c 0 : ℚ) ≠ 0 := by exact_mod_cast sdDelta_ne _ hD hc
  unfold sdN
  simp only [taDesign_cs, if_neg hc, taDesign_Q, Nat.cast_one, one_pow]
  by_cases hc' : c' = 0
  · subst hc'
    simp [h1', h2]
  · simp only [if_neg hc']
    have h3 : (sdDelta (taDesign s 1) 0 c' : ℚ) ≠ 0 := by exact_mod_cast sdDelta_ne _ hD (Ne.symm hc')
    simp [h1, h2, h3]

lemma taW_pos (δ : ℕ) {c c' : Fin s} (h : c ≠ c') : 0 < taW s δ c c' := by
  unfold taW
  have := abs_pos.mpr (taG_ne δ h)
  split_ifs <;> positivity

lemma taW_nonneg (δ : ℕ) (c c' : Fin s) : 0 ≤ taW s δ c c' := by
  unfold taW; split_ifs <;> positivity

lemma stCoef_row_cs {s : ℕ} (D : StagData s) {c' r : Fin s} (h : r = D.cs) :
    stCoef D c' r = (D.nI r c').natAbs := by simp [stCoef, h]

lemma stCoef_col_cs {s : ℕ} (D : StagData s) {c' r : Fin s} (h : c' = D.cs) :
    stCoef D c' r = (D.nI r c').natAbs := by simp [stCoef, h]

lemma stCoef_other {s : ℕ} (D : StagData s) {c' r : Fin s} (h1 : c' ≠ D.cs) (h2 : r ≠ D.cs) :
    stCoef D c' r = 2 * (D.nI r c').natAbs := by simp [stCoef, h1, h2]

lemma sdData_nI_cs {s : ℕ} (D : StagDesign s) (δ L : ℕ) (rows : Fin s → ℕ → Fin s) (e1 e2 e3 u : ℚ)
    {c c' : Fin s} (h : c = D.cs) : (sdData D δ L rows e1 e2 e3 u).nI c c' = ((L : ℚ) / D.Q c').num := by
  simp [sdData, h]

lemma sdData_nI_ne {s : ℕ} (D : StagDesign s) (δ L : ℕ) (rows : Fin s → ℕ → Fin s) (e1 e2 e3 u : ℚ)
    {c c' : Fin s} (h : c ≠ D.cs) : (sdData D δ L rows e1 e2 e3 u).nI c c' = (sdN D δ L c c').num := by
  simp [sdData, h]

/-- **The steps of the design** (proof of `thm:A`): the step of row `c` in column `c'`, divided by `T`, is
`L R^{c-c'} w(c,c')`, i.e. `stCoef · R^{c'} = L R^c w(c,c')`. -/
theorem stCoef_ta (R : ℕ) (hR : R % 2 = 1) (δ L : ℕ) (hL : sdLOK (taDesign s R) δ L) (rows : Fin s → ℕ → Fin s)
    (e1 e2 e3 u : ℚ) {c c' : Fin s} (h : c ≠ c') :
    (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c : ℚ) * (R : ℚ) ^ (c' : ℕ) =
      L * (R : ℚ) ^ (c : ℕ) * taW s δ c c' := by
  have hD := taDesign_ok (s := s) R hR
  have hR0 : 0 < R := by omega
  have hRq : (0 : ℚ) < (R : ℚ) ^ (c' : ℕ) := by positivity
  have habs : ∀ z : ℤ, ((z.natAbs : ℕ) : ℚ) = |(z : ℚ)| := fun z => by
    rw [Nat.cast_natAbs, Int.cast_abs]
  set SD := sdData (taDesign s R) δ L rows e1 e2 e3 u with hSD
  by_cases hc : c = 0
  · subst hc
    have hc' : c' ≠ 0 := Ne.symm h
    have hx := (lemR_half _ hD δ L hL (j := c') hc').1
    rw [stCoef_row_cs SD (show (0 : Fin s) = SD.cs from rfl),
      sdData_nI_cs _ δ L rows e1 e2 e3 u (show (0 : Fin s) = (taDesign s R).cs from rfl), habs,
      Rat.coe_int_num_of_den_eq_one hx, taDesign_Q, abs_of_nonneg (by positivity)]
    unfold taW taG
    simp only [if_pos rfl, or_true, if_true, abs_one, mul_one, Fin.val_zero, pow_zero]
    field_simp
  · have hn := lemR_int _ δ L hL (c := c) (c' := c') hc h
    have hs := sdN_ta R hR0 δ L hc (c' := c')
    have hc2 : c ≠ (taDesign s R).cs := hc
    unfold taW taG
    rw [if_neg hc]
    by_cases hc' : c' = 0
    · rw [stCoef_col_cs SD (show c' = SD.cs from hc'), sdData_nI_ne _ δ L rows e1 e2 e3 u hc2, habs,
        Rat.coe_int_num_of_den_eq_one hn]
      rw [if_pos (Or.inl hc'), mul_one]
      rw [← abs_of_pos hRq, ← abs_mul, hs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ L),
        abs_of_nonneg (by positivity : (0 : ℚ) ≤ (R : ℚ) ^ (c : ℕ))]
    · rw [stCoef_other SD (show c' ≠ SD.cs from hc') hc2, sdData_nI_ne _ δ L rows e1 e2 e3 u hc2]
      rw [if_neg (not_or.mpr ⟨hc', hc⟩)]
      push_cast
      rw [habs, Rat.coe_int_num_of_den_eq_one hn]
      rw [mul_assoc, ← abs_of_pos hRq, ← abs_mul, hs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ L),
        abs_of_nonneg (by positivity : (0 : ℚ) ≤ (R : ℚ) ^ (c : ℕ))]
      ring

end Design


/-! ## Rows, ratios, the geometric hierarchy -/

section Rows

variable {s : ℕ}

lemma taRows_val (c' : Fin s) (t : ℕ) :
    (taRows s c' t : ℕ) = if t + (c' : ℕ) + 1 < s then s - 1 - t else s - 2 - t := by
  unfold taRows; split_ifs <;> rfl

lemma taRows_ne (c' : Fin s) {t : ℕ} (ht : t < s - 1) : taRows s c' t ≠ c' := by
  intro h
  have := congrArg Fin.val h
  rw [taRows_val] at this
  split_ifs at this <;> omega

lemma taRows_mem (c' c : Fin s) (h : c ≠ c') : ∃ t < s - 1, taRows s c' t = c := by
  have hv : (c : ℕ) ≠ c' := fun e => h (Fin.ext e)
  have hc := c.2
  have hc' := c'.2
  rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
  · refine ⟨s - 2 - c, by omega, Fin.ext ?_⟩
    rw [taRows_val]; split_ifs <;> omega
  · refine ⟨s - 1 - c, by omega, Fin.ext ?_⟩
    rw [taRows_val]; split_ifs <;> omega

lemma taRows_lt (c' : Fin s) {t : ℕ} (ht : t + 1 < s - 1) : (taRows s c' (t + 1) : ℕ) < taRows s c' t := by
  rw [taRows_val, taRows_val]
  split_ifs <;> omega

end Rows

section Ratio

variable {s : ℕ} [NeZero s]

/-- **Consecutive steps** (proof of `thm:A`): for rows `c₂ < c₁` of column `c'`,
`stCoef(c₂) · R · w(c₁) ≤ stCoef(c₁) · w(c₂)` (the exponent drops by at least one). -/
theorem coef_ratio (R : ℕ) (hR : R % 2 = 1) (δ L : ℕ) (hL : sdLOK (taDesign s R) δ L) (rows : Fin s → ℕ → Fin s)
    (e1 e2 e3 u : ℚ) {c1 c2 c' : Fin s} (h1 : c1 ≠ c') (h2 : c2 ≠ c') (hlt : (c2 : ℕ) < c1) :
    (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c2 : ℚ) * R * taW s δ c1 c' ≤
      (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c1 : ℚ) * taW s δ c2 c' := by
  have q1 := stCoef_ta R hR δ L hL rows e1 e2 e3 u h1
  have q2 := stCoef_ta R hR δ L hL rows e1 e2 e3 u h2
  have hR1 : (1 : ℚ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hP : (0 : ℚ) < (R : ℚ) ^ (c' : ℕ) := by positivity
  have hpow : (R : ℚ) ^ (c2 : ℕ) * R ≤ (R : ℚ) ^ (c1 : ℕ) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hR1 (by omega)
  have hw1 := taW_nonneg δ c1 c' (s := s)
  have hw2 := taW_nonneg δ c2 c' (s := s)
  refine le_of_mul_le_mul_right ?_ hP
  set S1 := (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c1 : ℚ)
  set S2 := (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c2 : ℚ)
  calc S2 * R * taW s δ c1 c' * (R : ℚ) ^ (c' : ℕ)
        = (S2 * (R : ℚ) ^ (c' : ℕ)) * R * taW s δ c1 c' := by ring
    _ = (L : ℚ) * ((R : ℚ) ^ (c2 : ℕ) * R) * (taW s δ c1 c' * taW s δ c2 c') := by rw [q2]; ring
    _ ≤ (L : ℚ) * (R : ℚ) ^ (c1 : ℕ) * (taW s δ c1 c' * taW s δ c2 c') := by gcongr
    _ = S1 * taW s δ c2 c' * (R : ℚ) ^ (c' : ℕ) := by
      rw [show S1 * taW s δ c2 c' * (R : ℚ) ^ (c' : ℕ) = (S1 * (R : ℚ) ^ (c' : ℕ)) * taW s δ c2 c' by ring, q1]
      ring

lemma taB_ge (δ : ℕ) (c c' : Fin s) : taW s δ c c' ≤ taB s δ ∧ (taW s δ c c')⁻¹ ≤ taB s δ := by
  have hn : ∀ c c' : Fin s, 0 ≤ taW s δ c c' + (taW s δ c c')⁻¹ := fun c c' => by
    have := taW_nonneg δ c c' (s := s); positivity
  have h1 : taW s δ c c' + (taW s δ c c')⁻¹ ≤ taB s δ := by
    unfold taB
    refine le_trans ?_ (Finset.single_le_sum (fun c _ => Finset.sum_nonneg fun c' _ => hn c c') (mem_univ c))
    exact Finset.single_le_sum (fun c' _ => hn c c') (mem_univ c')
  have := taW_nonneg δ c c' (s := s)
  constructor <;> nlinarith [inv_nonneg.mpr this]

/-- With `R ρ ≥ B²`, consecutive steps of a column (rows `c₂ < c₁`) satisfy `stCoef(c₂) ≤ ρ stCoef(c₁)`. -/
lemma coef_step (R : ℕ) (hR : R % 2 = 1) (δ L : ℕ) (hL : sdLOK (taDesign s R) δ L) (rows : Fin s → ℕ → Fin s)
    (e1 e2 e3 u ρ : ℚ) (hRρ : taB s δ ^ 2 ≤ R * ρ) {c1 c2 c' : Fin s} (h1 : c1 ≠ c') (h2 : c2 ≠ c')
    (hlt : (c2 : ℕ) < c1) :
    (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c2 : ℚ) ≤
      ρ * stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c1 := by
  have hr := coef_ratio R hR δ L hL rows e1 e2 e3 u h1 h2 hlt
  set S1 := (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c1 : ℚ)
  set S2 := (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c2 : ℚ)
  have hw1 := taW_pos δ h1 (s := s)
  obtain ⟨hb2, -⟩ := taB_ge δ c2 c' (s := s)
  obtain ⟨-, hb1⟩ := taB_ge δ c1 c' (s := s)
  have hS1 : 0 ≤ S1 := Nat.cast_nonneg _
  have hS2 : 0 ≤ S2 := Nat.cast_nonneg _
  have hR0 : (0 : ℚ) < R := by exact_mod_cast (show 0 < R by omega)
  have hw1i : 0 < (taW s δ c1 c')⁻¹ := inv_pos.mpr hw1
  -- `S2 R ≤ S1 w₂ w₁⁻¹ ≤ S1 B²`
  have hA : S2 * R ≤ S1 * (taW s δ c2 c' * (taW s δ c1 c')⁻¹) := by
    have := mul_le_mul_of_nonneg_right hr hw1i.le
    rwa [mul_assoc (S2 * R), mul_inv_cancel₀ hw1.ne', mul_one, mul_assoc] at this
  have hB0 : 0 ≤ taB s δ := le_trans (taW_nonneg δ c1 c') (taB_ge δ c1 c').1
  have hB : taW s δ c2 c' * (taW s δ c1 c')⁻¹ ≤ taB s δ ^ 2 := by
    rw [sq]; exact mul_le_mul hb2 hb1 hw1i.le hB0
  have hC : S2 * R ≤ S1 * (R * ρ) := le_trans hA (le_trans (mul_le_mul_of_nonneg_left hB hS1)
    (mul_le_mul_of_nonneg_left hRρ hS1))
  nlinarith

end Ratio

section Hier

variable {s : ℕ}

/-- **The geometric series of the proof of `thm:A`**: in a column whose rows all have the fraction `ε < ½`, with
positive steps, `μ_1 ≤ ε` and consecutive ratios `μ_{t+1} ≤ ρ μ_t`, `ρ(1 + ε) ≤ ε` (i.e. the steps differ by a
factor at least `1 + 1/ε`), every `N̄_{t-1} μ_t ≤ ε`. -/
theorem hier_geom (D : StagData s) (c' : Fin s) (ε ρ : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρε : ρ * (1 + ε) ≤ ε) (hlam : stLam (K := ℝ) D c' 0 = 2 * ε)
    (hpos : ∀ t < s - 1, 0 < stMu (K := ℝ) D c' t) (hμ0 : stMu (K := ℝ) D c' 0 ≤ ε)
    (hρ : ∀ t, t + 1 < s - 1 → stMu (K := ℝ) D c' (t + 1) ≤ ρ * stMu D c' t) :
    ∀ t, t + 1 < s - 1 → stNbar (K := ℝ) D c' t * stMu D c' (t + 1) ≤ ε := by
  have hρle : ρ ≤ ε := by nlinarith
  intro t
  induction t with
  | zero =>
    intro h1
    have ha := hpos 0 (by omega)
    have hb := hpos 1 h1
    have hr := hρ 0 h1
    have e : stNbar (K := ℝ) D c' 0 * stMu (K := ℝ) D c' 1 =
        (2 * stMu (K := ℝ) D c' 0 + 1 - 2 * ε) * (stMu (K := ℝ) D c' 1 / stMu (K := ℝ) D c' 0) := by
      have := ha.ne'
      simp only [stNbar, hlam]; field_simp; ring
    set a := stMu (K := ℝ) D c' 0
    set b := stMu (K := ℝ) D c' 1
    rw [e]
    have hba : b / a ≤ ρ := by rw [div_le_iff₀ ha]; linarith
    have hba0 : 0 ≤ b / a := by positivity
    have hX0 : 0 ≤ 2 * a + 1 - 2 * ε := by linarith
    have hX1 : 2 * a + 1 - 2 * ε ≤ 1 := by linarith
    calc (2 * a + 1 - 2 * ε) * (b / a) ≤ 1 * ρ := mul_le_mul hX1 hba hba0 zero_le_one
      _ ≤ ε := by linarith
  | succ t ih =>
    intro h1
    have ih' := ih (by omega)
    have ha := hpos (t + 1) (by omega)
    have hr := hρ (t + 1) h1
    have e : stNbar (K := ℝ) D c' (t + 1) * stMu (K := ℝ) D c' (t + 1 + 1) =
        (stNbar (K := ℝ) D c' t * stMu (K := ℝ) D c' (t + 1) + 1) *
          (stMu (K := ℝ) D c' (t + 1 + 1) / stMu (K := ℝ) D c' (t + 1)) := by
      have := ha.ne'
      simp only [stNbar]; field_simp
    set a := stMu (K := ℝ) D c' (t + 1)
    set b := stMu (K := ℝ) D c' (t + 1 + 1)
    rw [e]
    have hba : b / a ≤ ρ := by rw [div_le_iff₀ ha]; linarith
    have hb0 := hpos (t + 1 + 1) h1
    have hba0 : 0 ≤ b / a := by positivity
    by_cases hX : 0 ≤ stNbar (K := ℝ) D c' t * a + 1
    · calc (stNbar (K := ℝ) D c' t * a + 1) * (b / a) ≤ (ε + 1) * ρ := mul_le_mul (by linarith) hba hba0 (by linarith)
        _ ≤ ε := by linarith
    · push Not at hX
      nlinarith

end Hier


/-! ## `prop:P0` at a natural threshold above the data -/

section Big

variable {s : ℕ}

/-- **`prop:P0`, consequence, at a natural threshold** (used by `thm:A` and the `s = 4, 5` designs): if `𝒫(p₀)`
holds at a natural number `p₀` exceeding the place differences, the numerators and denominators of the `Q_j` and
`L`, and `u < 1`, then for every prime `p ≥ p₀` the local roots of the frame (scale `θ = 2^δ L T`) exist, and for
every choice of them the conclusion of `P0_design` holds with `C'' = M⋆^+(p₀)`. -/
theorem P0_big (D : StagDesign s) (hs : 2 ≤ s) (hD : sdOK D) (δ L : ℕ) (hL : sdLOK D δ L)
    (rows : Fin s → ℕ → Fin s) (eCS eCC eSC u : ℚ) (hv : (sdData D δ L rows eCS eCC eSC u).Valid)
    (hu1 : u < 1) (p0 : ℕ) (hP0 : StP (sdData D δ L rows eCS eCC eSC u) (p0 : ℚ))
    (hba : ∀ b c : Fin s, |frameA D.fr b - frameA D.fr c| < p0)
    (hbQ : ∀ j, j ≠ D.cs → |(D.Q j).num| < p0 ∧ (D.Q j).den < p0) (hbL : L < p0)
    (p : ℕ) [Fact p.Prime] (hp : p0 ≤ p) :
    (∃ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) ∧
    ∀ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) →
      (∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) →
      (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) ≤ stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) ∧
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
          (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N
            (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))) ≤
            Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))))) ∧
      ∀ g : Fin s → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam D p δ c) →
        RespInS (ssGen g zθ) (stWin (sdData D δ L rows eCS eCC eSC u) p) →
        IsSeq0 (zcode p) (ssGen g zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
          (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
          (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
            Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  set SD := sdData D δ L rows eCS eCC eSC u with hSD
  have hp0pos : (0 : ℝ) < p0 := by exact_mod_cast (show 0 < p0 by omega)
  have hP0R : StP SD (p0 : ℝ) := by
    have := (StP_cast SD (p0 : ℚ)).mp hP0
    rwa [Rat.cast_natCast] at this
  have hpp : (p0 : ℝ) ≤ p := by exact_mod_cast hp
  have hpR : (0 : ℝ) < p := lt_of_lt_of_le hp0pos hpp
  have hP := (P0_mono SD hp0pos hpp hP0R).1
  have hT := stT_facts u p hP.1
  have hTp : stT u p < p := by
    have h1 : (u : ℝ) < 1 := by exact_mod_cast hu1
    have : (stT u p : ℝ) < p := by nlinarith [hT.2.2.1]
    exact_mod_cast this
  have hpT : (stT u p : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by have := hT.1; omega) hTp
  have hpi : (p0 : ℤ) ≤ p := by exact_mod_cast hp
  have hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0 := fun b c h =>
    intCast_ne_zero_of_abs_lt _ (sub_ne_zero.mpr (hD.1 b c h)) (lt_of_lt_of_le (hba b c) hpi)
  have hpQ : ∀ j, j ≠ D.cs → ((D.Q j).num : ZMod p) ≠ 0 ∧ ((D.Q j).den : ZMod p) ≠ 0 := fun j hj => by
    obtain ⟨hn, hd⟩ := hbQ j hj
    refine ⟨intCast_ne_zero_of_abs_lt _ (Rat.num_ne_zero.mpr (hD.2 j hj).1.ne') (lt_of_lt_of_le hn hpi), ?_⟩
    exact natCast_ne_zero_of_lt (D.Q j).den_pos (lt_of_lt_of_le hd hp)
  have hpL : (L : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by have := hL.1; omega) (lt_of_lt_of_le hbL hp)
  have hroots := frame_roots_exist p s D.fr
    (fun c hc b hb => by
      have hne := sub_ne_zero.mpr (hD.1 ⟨c, hc⟩ ⟨b, by omega⟩ (fun e => by
        have := congrArg Fin.val e; simp at this; omega))
      intro h0
      exact hne (Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero h0)
        (lt_of_lt_of_le (hba ⟨c, hc⟩ ⟨b, by omega⟩) hpi)))
    (sdTheta p δ L (stT u p))
  refine ⟨hroots, fun zθ hroot hplace => ?_⟩
  exact P0_design D hs hD δ L hL rows eCS eCC eSC u hv (p0 : ℝ) hp0pos hP0R p hpp hpa hpQ hpL hpT zθ hroot hplace

end Big

/-! ## `thm:A` -/

section MainA

theorem eps10_lt (s : ℕ) (hs : 3 ≤ s) : 1 / (10 * (s : ℝ)) < epsS s := by
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  rw [epsS_lt_iff]
  have hf := epsS_factor s (1 / (10 * (s : ℝ)))
  set d := Real.sqrt (3 * (s : ℝ) ^ 2 + 4 * s)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have e1 : (s : ℝ) * (1 / (10 * s)) = 1 / 10 := by field_simp
  have e2 : 1 / (10 * (s : ℝ)) ≤ 1 / 30 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have e3 : 0 < 1 / (10 * (s : ℝ)) := by positivity
  have hG : 0 < (1 - s * (1 / (10 * s))) ^ 2 + (1 / 2 - 1 / (10 * (s : ℝ))) ^ 2 - 1 := by
    rw [e1]; nlinarith
  have hA : 2 * ((s : ℝ) ^ 2 + 1) * (1 / (10 * s)) - (2 * s + 1) < 0 := by
    have : 2 * ((s : ℝ) ^ 2 + 1) * (1 / (10 * s)) = ((s : ℝ) ^ 2 + 1) / (5 * s) := by field_simp; ring
    rw [this, sub_neg, div_lt_iff₀ (by positivity)]; nlinarith
  have hpos : 0 < 4 * ((s : ℝ) ^ 2 + 1) *
      ((1 - s * (1 / (10 * s))) ^ 2 + (1 / 2 - 1 / (10 * (s : ℝ))) ^ 2 - 1) := by positivity
  rw [hf] at hpos
  by_contra h
  push Not at h
  have := mul_nonpos_of_nonpos_of_nonneg (by linarith : 2 * ((s : ℝ) ^ 2 + 1) * (1 / (10 * s)) - (2 * s + 1) - d ≤ 0) h
  linarith

variable {s : ℕ} [NeZero s]

omit [NeZero s] in
lemma natAbs_le_coef (D : StagData s) (c c' : Fin s) : (D.nI c c').natAbs ≤ stCoef D c' c := by
  unfold stCoef; split_ifs <;> omega

lemma taData_valid (R : ℕ) (hR : R % 2 = 1) (δ L : ℕ) (hL : sdLOK (taDesign s R) δ L) (e1 e2 e3 u : ℚ) :
    (sdData (taDesign s R) δ L (taRows s) e1 e2 e3 u).Valid := by
  have hD := taDesign_ok (s := s) R hR
  refine ⟨fun c' t ht => taRows_ne c' ht, fun c' c h => ?_, fun c c' h => ?_, fun i hi => ?_⟩
  · obtain ⟨t, ht, he⟩ := taRows_mem c' c h
    exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, he⟩
  · by_cases hc : c = 0
    · rw [sdData_nI_cs _ δ L _ e1 e2 e3 u hc]
      have hc' : c' ≠ (taDesign s R).cs := by rw [taDesign_cs]; rw [hc] at h; exact Ne.symm h
      have := (lemR_half _ hD δ L hL hc').2.1
      intro h0; rw [h0] at this; simp at this
    · rw [sdData_nI_ne _ δ L _ e1 e2 e3 u hc]
      refine Rat.num_ne_zero.mpr fun h0 => ?_
      have hs := sdN_ta R (by omega) δ L hc (c' := c')
      rw [h0, zero_mul] at hs
      have hG := taG_ne δ h (s := s)
      unfold taG at hG
      rw [if_neg hc] at hG
      have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by have := hL.1; omega)
      have hR0 : (R : ℚ) ^ (c : ℕ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show R ≠ 0 by omega))
      exact (mul_ne_zero (mul_ne_zero hL0 hR0) hG) hs.symm
  · rw [sdData_nI_cs (taDesign s R) δ L (taRows s) e1 e2 e3 u
      (c := (sdData (taDesign s R) δ L (taRows s) e1 e2 e3 u).cs) (c' := i) rfl]
    exact (lemR_half _ hD δ L hL hi).2.1


/-- **`thm:A`** (separation `1 - O(1/p)` in every dimension): for every `s ≥ 3` there are a staggered design on the
Faure places `(0, 1, …, s-1)` (staggered coordinate `0`, natural order of `C`, `Q_r = R^r` with an odd `R`), its
`δ`, `L` (the least values of `lem:R`), the row orders of decreasing steps, a uniform rational window fraction
`ε < ε_s`, a rational `u > 0` and a natural number `p₀` with `𝒫(p₀)` (an exact, decidable rational statement, so
`p₀(s)` is effectively computable; the design satisfies the limit hierarchy) such that for every prime `p ≥ p₀` (no
congruence condition) the local roots exist and, for every choice of them, the staggered rule (`def:BS`) gives:
selection rules exist, and every selection rule — and every multiplier family with the constants of `lem:R` and all
responses in the windows — gives a digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ 1 - C''_s/p` for every
`K ≥ 1`, `C''_s = M⋆^+(p₀)`, quasi-uniform (`h(P_{[N]}) ≤ (√s p/(1 - C''_s/p)) · 2δ(P_{[N]})`, `lem:prefix`). -/
theorem A (s : ℕ) (hs : 3 ≤ s) :
    ∃ (D : StagDesign s) (R δ L : ℕ) (rows : Fin s → ℕ → Fin s) (ε u : ℚ) (p0 : ℕ),
      D.fr = faureFr s ∧ (D.cs : ℕ) = 0 ∧ R % 2 = 1 ∧ (∀ j : Fin s, j ≠ D.cs → D.Q j = (R : ℚ) ^ (j : ℕ)) ∧
      sdOK D ∧ IsLeast {δ | sdDeltaOK D δ} δ ∧ IsLeast {L | sdLOK D δ L} L ∧
      0 < ε ∧ (ε : ℝ) < epsS s ∧ 0 < u ∧ (sdData D δ L rows ε ε ε u).Valid ∧
      (∀ c' : Fin s, ∀ t, t + 1 < s - 1 → stCoef (sdData D δ L rows ε ε ε u) c' (rows c' (t + 1)) < stCoef (sdData D δ L rows ε ε ε u) c' (rows c' t)) ∧
      LimHier (K := ℝ) (sdData D δ L rows ε ε ε u) ∧ StP (sdData D δ L rows ε ε ε u) (p0 : ℚ) ∧
      ∀ (p : ℕ) [Fact p.Prime], p0 ≤ p →
        (∃ zθ : Fin s → PowerSeries (ZMod p),
          (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) ∧
          ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) ∧
        ∀ zθ : Fin s → PowerSeries (ZMod p),
          (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) →
          (∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) →
          (stMv (sdData D δ L rows ε ε ε u) p D.cs : ℝ) ≤ stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) ∧
          (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
            IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows ε ε ε u) p) rule) ∧
          (∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
            IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows ε ε ε u) p) rule →
            IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
              (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
              (1 - (stMv (sdData D δ L rows ε ε ε u) p D.cs : ℝ) / p)) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
              (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
              (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p)) ∧
            ∀ N : ℕ, 2 ≤ N →
              Z3NetDGS.covRad euclDist (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))) ≤
                Real.sqrt s * p / (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p) *
                  (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                    (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))))) ∧
          ∀ g : Fin s → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam D p δ c) →
            RespInS (ssGen g zθ) (stWin (sdData D δ L rows ε ε ε u) p) →
            IsSeq0 (zcode p) (ssGen g zθ) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ)) (1 - (stMv (sdData D δ L rows ε ε ε u) p D.cs : ℝ) / p)) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ)) (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p)) ∧
            ∀ N : ℕ, 2 ≤ N →
              Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
                Real.sqrt s * p / (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p) *
                  (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  haveI : NeZero s := ⟨by omega⟩
  have hs2 : 2 ≤ s := by omega
  have hsQ : (3 : ℚ) ≤ s := by exact_mod_cast hs
  obtain ⟨δ, hδ⟩ := lemR_delta (taDesign s 1)
  set ε : ℚ := 1 / (10 * s) with hεdef
  have hε0 : 0 < ε := by positivity
  have hε30 : ε ≤ 1 / 30 := by rw [hεdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hsε : (s : ℚ) * ε = 1 / 10 := by rw [hεdef]; field_simp
  set ρ : ℚ := ε / (1 + ε) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρε : ρ * (1 + ε) = ε := by rw [hρdef]; field_simp
  set R : ℕ := 2 * ⌈taB s δ ^ 2 / ρ⌉₊ + 1 with hRdef
  have hR : R % 2 = 1 := by omega
  have hR1 : 1 ≤ R := by omega
  have hRρ : taB s δ ^ 2 ≤ R * ρ := by
    have h1 := Nat.le_ceil (taB s δ ^ 2 / ρ)
    have h2 : (⌈taB s δ ^ 2 / ρ⌉₊ : ℚ) ≤ R := by rw [hRdef]; push_cast; linarith [Nat.cast_nonneg (α := ℚ) ⌈taB s δ ^ 2 / ρ⌉₊]
    rw [div_le_iff₀ hρ0] at h1
    nlinarith
  have hDR := taDesign_ok (s := s) R hR
  have hδR : IsLeast {δ | sdDeltaOK (taDesign s R) δ} δ := hδ
  obtain ⟨L, hLl⟩ := lemR_L (taDesign s R) hDR δ hδR.1
  have hL := hLl.1
  have hL1 : 1 ≤ L := by have := hL.1; omega
  -- the steps divided by `T` (independent of `u`)
  set S : ℕ := ∑ c' : Fin s, ∑ c : Fin s, stCoef (sdData (taDesign s R) δ L (taRows s) ε ε ε 0) c' c with hSdef
  have hcoefS : ∀ (v : ℚ) (c' c : Fin s), stCoef (sdData (taDesign s R) δ L (taRows s) ε ε ε v) c' c ≤ S :=
    fun v c' c => le_trans (Finset.single_le_sum (f := fun c => stCoef (sdData (taDesign s R) δ L (taRows s) ε ε ε 0) c' c)
      (fun _ _ => Nat.zero_le _) (mem_univ c))
      (Finset.single_le_sum (f := fun c' => ∑ c : Fin s, stCoef (sdData (taDesign s R) δ L (taRows s) ε ε ε 0) c' c)
        (fun _ _ => Nat.zero_le _) (mem_univ c'))
  have hS1 : 1 ≤ S := le_trans (valid_coef _ (taData_valid R hR δ L hL ε ε ε 0) 0 (t := 0) (by omega)) (hcoefS 0 _ _)
  set u : ℚ := ε / (2 * S) with hudef
  have hSq : (1 : ℚ) ≤ S := by exact_mod_cast hS1
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := by
    rw [hudef, div_lt_one (by positivity)]; linarith
  set SD := sdData (taDesign s R) δ L (taRows s) ε ε ε u with hSD
  have hv : SD.Valid := taData_valid R hR δ L hL ε ε ε u
  have hSDu : SD.u = u := rfl
  have hstep : ∀ c' c : Fin s, (stCoef SD c' c : ℚ) * u ≤ ε / 2 := fun c' c => by
    have h := hcoefS u c' c
    have : (stCoef SD c' c : ℚ) ≤ S := by exact_mod_cast h
    calc (stCoef SD c' c : ℚ) * u ≤ S * u := mul_le_mul_of_nonneg_right this hu0.le
      _ = ε / 2 := by rw [hudef]; field_simp
  have hfrac : ∀ c' r : Fin s, stFrac SD c' r = ε := fun c' r => by
    simp only [stFrac, hSD, sdData]; split_ifs <;> rfl
  -- consecutive steps
  have hratio : ∀ c' : Fin s, ∀ t, t + 1 < s - 1 →
      (stCoef SD c' (taRows s c' (t + 1)) : ℚ) ≤ ρ * stCoef SD c' (taRows s c' t) := fun c' t ht =>
    coef_step R hR δ L hL (taRows s) ε ε ε u ρ hRρ (taRows_ne c' (by omega)) (taRows_ne c' ht) (taRows_lt c' ht)
  have hdec : ∀ c' : Fin s, ∀ t, t + 1 < s - 1 →
      stCoef SD c' (taRows s c' (t + 1)) < stCoef SD c' (taRows s c' t) := fun c' t ht => by
    have h1 := hratio c' t ht
    have h2 : (1 : ℚ) ≤ stCoef SD c' (taRows s c' t) := by exact_mod_cast valid_coef SD hv c' (t := t) (by omega)
    have hρ1 : ρ < 1 := by rw [hρdef, div_lt_one (by positivity)]; linarith
    have : (stCoef SD c' (taRows s c' (t + 1)) : ℚ) < stCoef SD c' (taRows s c' t) := by nlinarith
    exact_mod_cast this
  -- the limit hierarchy
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hstepR : ∀ c' c : Fin s, (stCoef SD c' c : ℝ) * (u : ℝ) ≤ (ε : ℝ) / 2 := fun c' c => by
    have := hstep c' c
    have h := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at h; exact h
  have hε2R : (ε : ℝ) < 1 / 2 := by
    have : ε < 1 / 2 := by linarith
    have h := (Rat.cast_lt (K := ℝ)).mpr this
    rwa [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by push_cast; ring] at h
  have hρ0R : (0 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ0.le
  have hρεR : (ρ : ℝ) * (1 + ε) ≤ ε := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) hρε; push_cast at h; linarith
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu0
  have hH : LimHier (K := ℝ) SD := by
    refine ⟨fun c' => ⟨?_, fun t ht => ?_⟩, fun c c' hc hcc => ?_, fun i hi => ?_⟩
    · have := hstepR c' (SD.rows c' 0)
      simp only [stMu, stLam, hfrac, hSDu]
      linarith
    · have hg := hier_geom SD c' (ε : ℝ) (ρ : ℝ) hεR hε2R hρ0R hρεR (by simp only [stLam, hfrac])
        (fun t ht => by
          have h2 : (1 : ℝ) ≤ stCoef SD c' (SD.rows c' t) := by exact_mod_cast valid_coef SD hv c' ht
          simp only [stMu]; positivity)
        (by have := hstepR c' (SD.rows c' 0); simp only [stMu, hSDu]; linarith)
        (fun t ht => by
          have h := (Rat.cast_le (K := ℝ)).mpr (hratio c' t ht)
          push_cast at h
          simp only [stMu]
          change (stCoef SD c' (taRows s c' (t + 1)) : ℝ) * u ≤ ρ * ((stCoef SD c' (taRows s c' t) : ℝ) * u)
          nlinarith)
        t (by omega)
      simp only [stLam, hfrac]
      push_cast
      linarith
    · have h1 : ((SD.nI c c').natAbs : ℝ) ≤ stCoef SD c' c := by exact_mod_cast natAbs_le_coef SD c c'
      have h2 := hstepR c' c
      have : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0.le
      rw [hfrac, hSDu]
      nlinarith
    · have h1 : ((SD.nI SD.cs i).natAbs : ℝ) ≤ stCoef SD i SD.cs := by exact_mod_cast natAbs_le_coef SD SD.cs i
      have h2 := hstepR i SD.cs
      have : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0.le
      have he : SD.eSC = ε := rfl
      rw [he, hSDu]
      nlinarith
  -- `prop:P0`(c)
  have hsub : ((s - 2 : ℕ) : ℚ) = s - 2 := by rw [Nat.cast_sub hs2]; norm_num
  have hxy : 1 < stX SD ^ 2 + stY SD ^ 2 := by
    have hX : stX SD = 9 / 10 := by
      simp only [stX, hSD, sdData]; rw [hsub]; linarith
    have hY : stY SD = 1 / 2 - ε := rfl
    rw [hX, hY]; nlinarith
  have hz : 1 / Real.sqrt 2 < 1 - 2 * ((s - 2 : ℕ) : ℝ) * (SD.eCC : ℝ) - 2 * (SD.eCS : ℝ) := by
    have hsubR : ((s - 2 : ℕ) : ℝ) = s - 2 := by rw [Nat.cast_sub hs2]; norm_num
    have hsεR : (s : ℝ) * (ε : ℝ) = 1 / 10 := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) hsε; push_cast at h; linarith
    have hcc : (SD.eCC : ℝ) = ε := rfl
    have hcs : (SD.eCS : ℝ) = ε := rfl
    rw [hsubR, hcc, hcs]
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 : 0 < Real.sqrt 2 := by positivity
    rw [div_lt_iff₀ hs0]
    nlinarith
  have hSC2 : SD.eSC < 1 / 2 := by show ε < 1 / 2; linarith
  obtain ⟨p0, hp0N, -, hP0⟩ := P0_c_nat SD hs2 hv hu0 hε0 hε0 hε0 hSC2 hxy hz hH (s + R ^ s + L + 1)
  refine ⟨taDesign s R, R, δ, L, taRows s, ε, u, p0, rfl, rfl, hR, fun j _ => rfl, hDR, hδR, hLl, hε0, ?_, hu0,
    hv, hdec, hH, hP0, fun p _ hp => ?_⟩
  · have := eps10_lt s hs
    rw [hεdef]; push_cast; exact this
  refine P0_big (taDesign s R) hs2 hDR δ L hL (taRows s) ε ε ε u hv hu1 p0 hP0 (fun b c => ?_) (fun j _ => ?_)
    (by omega) p hp
  · show |frameA (faureFr s) b - frameA (faureFr s) c| < p0
    rw [frameA_faure b.2, frameA_faure c.2]
    have hb := b.2; have hc := c.2
    have : (s : ℤ) ≤ p0 := by exact_mod_cast (show s ≤ p0 by omega)
    rw [abs_lt]; constructor <;> push_cast <;> omega
  · rw [taQ_num, taQ_den]
    have hRj : R ^ (j : ℕ) ≤ R ^ s := Nat.pow_le_pow_right (by omega) j.2.le
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (show R ^ (j : ℕ) < p0 by omega)
    · omega

end MainA

end GeoSeq
