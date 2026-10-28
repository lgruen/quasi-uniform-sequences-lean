/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3

@[expose] public section

/-!
# GeoSeq stage V3: the table `tab:P1` (`s = 3, …, 7`)

For each `s = 3, …, 7` the rational point `u^*` of `tab:P1`: the exact rational inequalities `u_min < u^*`,
`F(u^*) < 1`, `Q_s^s u^{*s} ≤ P` (the column `p_1(s) ≤`), `Q_s^s (u^* F(u^*))^s ≤ C^s` (the column `C'_s`), and
`(Q - 0.005)^s < Q_s^s < (Q + 0.005)^s` (the column `Q_s`, two decimals) are checked by `decide +kernel` on the
computable rational `F` (the same definition as in the theorems, `mrF_cast`). `MRall_rat` then gives
`p_1(s) ≤ P`, `C'_s ≤ C`, and for every prime `p ≥ P` the mixed-radix rule has `Γ < p` and
`1 - (p-Γ)/p ≤ C p^{-1/s}` (`tabP1_s3`, …, `tabP1_s7`).
-/

namespace GeoSeq

/-- `Q_s` to two decimals from rational `s`-th powers. -/
theorem mrQ_bracket (s : ℕ) (hs : 2 ≤ s) (a b : ℚ) (ha : 0 ≤ a) (hb0 : 0 ≤ b) (h1 : a ^ s < mrQss s)
    (h2 : mrQss s < b ^ s) : (a : ℝ) < mrQ s ∧ mrQ s < b := by
  have hQ := (mrQ_pos s hs).le
  have hb : (0 : ℝ) ≤ b := by exact_mod_cast hb0
  constructor
  · refine (pow_lt_pow_iff_left₀ (by exact_mod_cast ha) hQ (by omega : s ≠ 0)).mp ?_
    rw [mrQ_pow s hs]; exact_mod_cast h1
  · refine (pow_lt_pow_iff_left₀ hQ hb (by omega : s ≠ 0)).mp ?_
    rw [mrQ_pow s hs]; exact_mod_cast h2

theorem tabP1_data3 :
    mrUmin 3 < (2934559 / 10 ^ 6 : ℚ) ∧ mrF 3 (2934559 / 10 ^ 6 : ℚ) < 1 ∧
      mrQss 3 * (2934559 / 10 ^ 6 : ℚ) ^ 3 ≤ 6318 / 100 ∧
      mrQss 3 * ((2934559 / 10 ^ 6 : ℚ) * mrF 3 (2934559 / 10 ^ 6 : ℚ)) ^ 3 ≤ (399 / 100) ^ 3 ∧
      (1355 / 1000 : ℚ) ^ 3 < mrQss 3 ∧ mrQss 3 < (1365 / 1000 : ℚ) ^ 3 := by
  decide +kernel

theorem tabP1_data4 :
    mrUmin 4 < (3495097 / 10 ^ 6 : ℚ) ∧ mrF 4 (3495097 / 10 ^ 6 : ℚ) < 1 ∧
      mrQss 4 * (3495097 / 10 ^ 6 : ℚ) ^ 4 ≤ 8899 / 10 ∧
      mrQss 4 * ((3495097 / 10 ^ 6 : ℚ) * mrF 4 (3495097 / 10 ^ 6 : ℚ)) ^ 4 ≤ (547 / 100) ^ 4 ∧
      (1555 / 1000 : ℚ) ^ 4 < mrQss 4 ∧ mrQss 4 < (1565 / 1000 : ℚ) ^ 4 := by
  decide +kernel

theorem tabP1_data5 :
    mrUmin 5 < (197527 / 62500 : ℚ) ∧ mrF 5 (197527 / 62500 : ℚ) < 1 ∧
      mrQss 5 * (197527 / 62500 : ℚ) ^ 5 ≤ 80579 / 10 ∧
      mrQss 5 * ((197527 / 62500 : ℚ) * mrF 5 (197527 / 62500 : ℚ)) ^ 5 ≤ (605 / 100) ^ 5 ∧
      (1905 / 1000 : ℚ) ^ 5 < mrQss 5 ∧ mrQss 5 < (1915 / 1000 : ℚ) ^ 5 := by
  decide +kernel

theorem tabP1_data6 :
    mrUmin 6 < (2270329 / 500000 : ℚ) ∧ mrF 6 (2270329 / 500000 : ℚ) < 1 ∧
      mrQss 6 * (2270329 / 500000 : ℚ) ^ 6 ≤ 8607 * 10 ^ 2 ∧
      mrQss 6 * ((2270329 / 500000 : ℚ) * mrF 6 (2270329 / 500000 : ℚ)) ^ 6 ≤ (976 / 100) ^ 6 ∧
      (2145 / 1000 : ℚ) ^ 6 < mrQss 6 ∧ mrQss 6 < (2155 / 1000 : ℚ) ^ 6 := by
  decide +kernel

theorem tabP1_data7 :
    mrUmin 7 < (1280189 / 250000 : ℚ) ∧ mrF 7 (1280189 / 250000 : ℚ) < 1 ∧
      mrQss 7 * (1280189 / 250000 : ℚ) ^ 7 ≤ 5322 * 10 ^ 4 ∧
      mrQss 7 * ((1280189 / 250000 : ℚ) * mrF 7 (1280189 / 250000 : ℚ)) ^ 7 ≤ (1270 / 100) ^ 7 ∧
      (2475 / 1000 : ℚ) ^ 7 < mrQss 7 ∧ mrQss 7 < (2485 / 1000 : ℚ) ^ 7 := by
  decide +kernel

/-- Assembly of one row of `tab:P1` from its exact rational data. -/
theorem tabP1_of (s : ℕ) (hs : 3 ≤ s) (us P C Qa Qb : ℚ)
    (hd : mrUmin s < us ∧ mrF s us < 1 ∧ mrQss s * us ^ s ≤ P ∧ mrQss s * (us * mrF s us) ^ s ≤ C ^ s ∧
      Qa ^ s < mrQss s ∧ mrQss s < Qb ^ s) (hC0 : 0 ≤ C) (hQa : 0 ≤ Qa) (hQb : 0 ≤ Qb) (hPs : (s : ℚ) ≤ P) :
    mrP1 s ≤ P ∧ mrCp s us ≤ C ∧ (Qa : ℝ) < mrQ s ∧ mrQ s < Qb ∧
      ∀ p : ℕ, p.Prime → (P : ℝ) ≤ p →
        mrCost s p (mrRuleH s p) < p ∧
          1 - ((p : ℝ) - mrCost s p (mrRuleH s p)) / p ≤ C * (p : ℝ) ^ (-(1 : ℝ) / s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  obtain ⟨hP1, hCp, hall⟩ := MRall_rat s hs us P C h1 h2 h3 hC0 h4
  obtain ⟨hQ1, hQ2⟩ := mrQ_bracket s (by omega) Qa Qb hQa hQb h5 h6
  refine ⟨hP1, hCp, hQ1, hQ2, fun p hp hPp => hall p hp hPp ?_⟩
  have : ((s : ℚ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPs
  have : (s : ℝ) ≤ p := by push_cast at this; linarith
  exact_mod_cast this

/-- **`tab:P1`, row `s = 3`**: `u^* = 2934559 / 10 ^ 6` has `u_min < u^*` and `F(u^*) < 1`; hence `p_1(3) ≤ 63.18`,
`C'_3 ≤ 3.99`, `Q_3 = 1.36` to two decimals, and for every prime `p ≥ 63.18` the mixed-radix rule has `Γ < p` and
`1 - (p-Γ)/p ≤ 3.99 p^{-1/3}` (`thm:MRall`(b),(c)). -/
theorem tabP1_s3 :
    mrUmin 3 < (2934559 / 10 ^ 6 : ℚ) ∧ mrF 3 (2934559 / 10 ^ 6 : ℚ) < 1 ∧
      mrP1 3 ≤ ((6318 / 100 : ℚ) : ℝ) ∧ mrCp 3 ((2934559 / 10 ^ 6 : ℚ) : ℝ) ≤ ((399 / 100 : ℚ) : ℝ) ∧
      ((1355 / 1000 : ℚ) : ℝ) < mrQ 3 ∧ mrQ 3 < ((1365 / 1000 : ℚ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → ((6318 / 100 : ℚ) : ℝ) ≤ p →
        mrCost 3 p (mrRuleH 3 p) < p ∧
          1 - ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p ≤ ((399 / 100 : ℚ) : ℝ) * (p : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hd := tabP1_data3
  obtain ⟨a, b, c, d, e⟩ := tabP1_of 3 (by norm_num) (2934559 / 10 ^ 6) (6318 / 100) (399 / 100) (1355 / 1000) (1365 / 1000) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hd.1, hd.2.1, a, b, c, d, fun p hp hPp => by have := e p hp hPp; exact_mod_cast this⟩

/-- **`tab:P1`, row `s = 4`**: `u^* = 3495097 / 10 ^ 6` has `u_min < u^*` and `F(u^*) < 1`; hence `p_1(4) ≤ 889.9`,
`C'_4 ≤ 5.47`, `Q_4 = 1.56` to two decimals, and for every prime `p ≥ 889.9` the mixed-radix rule has `Γ < p` and
`1 - (p-Γ)/p ≤ 5.47 p^{-1/4}` (`thm:MRall`(b),(c)). -/
theorem tabP1_s4 :
    mrUmin 4 < (3495097 / 10 ^ 6 : ℚ) ∧ mrF 4 (3495097 / 10 ^ 6 : ℚ) < 1 ∧
      mrP1 4 ≤ ((8899 / 10 : ℚ) : ℝ) ∧ mrCp 4 ((3495097 / 10 ^ 6 : ℚ) : ℝ) ≤ ((547 / 100 : ℚ) : ℝ) ∧
      ((1555 / 1000 : ℚ) : ℝ) < mrQ 4 ∧ mrQ 4 < ((1565 / 1000 : ℚ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → ((8899 / 10 : ℚ) : ℝ) ≤ p →
        mrCost 4 p (mrRuleH 4 p) < p ∧
          1 - ((p : ℝ) - mrCost 4 p (mrRuleH 4 p)) / p ≤ ((547 / 100 : ℚ) : ℝ) * (p : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hd := tabP1_data4
  obtain ⟨a, b, c, d, e⟩ := tabP1_of 4 (by norm_num) (3495097 / 10 ^ 6) (8899 / 10) (547 / 100) (1555 / 1000) (1565 / 1000) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hd.1, hd.2.1, a, b, c, d, fun p hp hPp => by have := e p hp hPp; exact_mod_cast this⟩

/-- **`tab:P1`, row `s = 5`**: `u^* = 197527 / 62500` has `u_min < u^*` and `F(u^*) < 1`; hence `p_1(5) ≤ 8057.9`,
`C'_5 ≤ 6.05`, `Q_5 = 1.91` to two decimals, and for every prime `p ≥ 8057.9` the mixed-radix rule has `Γ < p` and
`1 - (p-Γ)/p ≤ 6.05 p^{-1/5}` (`thm:MRall`(b),(c)). -/
theorem tabP1_s5 :
    mrUmin 5 < (197527 / 62500 : ℚ) ∧ mrF 5 (197527 / 62500 : ℚ) < 1 ∧
      mrP1 5 ≤ ((80579 / 10 : ℚ) : ℝ) ∧ mrCp 5 ((197527 / 62500 : ℚ) : ℝ) ≤ ((605 / 100 : ℚ) : ℝ) ∧
      ((1905 / 1000 : ℚ) : ℝ) < mrQ 5 ∧ mrQ 5 < ((1915 / 1000 : ℚ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → ((80579 / 10 : ℚ) : ℝ) ≤ p →
        mrCost 5 p (mrRuleH 5 p) < p ∧
          1 - ((p : ℝ) - mrCost 5 p (mrRuleH 5 p)) / p ≤ ((605 / 100 : ℚ) : ℝ) * (p : ℝ) ^ (-(1 : ℝ) / 5) := by
  have hd := tabP1_data5
  obtain ⟨a, b, c, d, e⟩ := tabP1_of 5 (by norm_num) (197527 / 62500) (80579 / 10) (605 / 100) (1905 / 1000) (1915 / 1000) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hd.1, hd.2.1, a, b, c, d, fun p hp hPp => by have := e p hp hPp; exact_mod_cast this⟩

/-- **`tab:P1`, row `s = 6`**: `u^* = 2270329 / 500000` has `u_min < u^*` and `F(u^*) < 1`; hence `p_1(6) ≤ 8.607·10⁵`,
`C'_6 ≤ 9.76`, `Q_6 = 2.15` to two decimals, and for every prime `p ≥ 8.607·10⁵` the mixed-radix rule has `Γ < p` and
`1 - (p-Γ)/p ≤ 9.76 p^{-1/6}` (`thm:MRall`(b),(c)). -/
theorem tabP1_s6 :
    mrUmin 6 < (2270329 / 500000 : ℚ) ∧ mrF 6 (2270329 / 500000 : ℚ) < 1 ∧
      mrP1 6 ≤ ((8607 * 10 ^ 2 : ℚ) : ℝ) ∧ mrCp 6 ((2270329 / 500000 : ℚ) : ℝ) ≤ ((976 / 100 : ℚ) : ℝ) ∧
      ((2145 / 1000 : ℚ) : ℝ) < mrQ 6 ∧ mrQ 6 < ((2155 / 1000 : ℚ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → ((8607 * 10 ^ 2 : ℚ) : ℝ) ≤ p →
        mrCost 6 p (mrRuleH 6 p) < p ∧
          1 - ((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p ≤ ((976 / 100 : ℚ) : ℝ) * (p : ℝ) ^ (-(1 : ℝ) / 6) := by
  have hd := tabP1_data6
  obtain ⟨a, b, c, d, e⟩ := tabP1_of 6 (by norm_num) (2270329 / 500000) (8607 * 10 ^ 2) (976 / 100) (2145 / 1000) (2155 / 1000) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hd.1, hd.2.1, a, b, c, d, fun p hp hPp => by have := e p hp hPp; exact_mod_cast this⟩

/-- **`tab:P1`, row `s = 7`**: `u^* = 1280189 / 250000` has `u_min < u^*` and `F(u^*) < 1`; hence `p_1(7) ≤ 5.322·10⁷`,
`C'_7 ≤ 12.70`, `Q_7 = 2.48` to two decimals, and for every prime `p ≥ 5.322·10⁷` the mixed-radix rule has `Γ < p` and
`1 - (p-Γ)/p ≤ 12.70 p^{-1/7}` (`thm:MRall`(b),(c)). -/
theorem tabP1_s7 :
    mrUmin 7 < (1280189 / 250000 : ℚ) ∧ mrF 7 (1280189 / 250000 : ℚ) < 1 ∧
      mrP1 7 ≤ ((5322 * 10 ^ 4 : ℚ) : ℝ) ∧ mrCp 7 ((1280189 / 250000 : ℚ) : ℝ) ≤ ((1270 / 100 : ℚ) : ℝ) ∧
      ((2475 / 1000 : ℚ) : ℝ) < mrQ 7 ∧ mrQ 7 < ((2485 / 1000 : ℚ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → ((5322 * 10 ^ 4 : ℚ) : ℝ) ≤ p →
        mrCost 7 p (mrRuleH 7 p) < p ∧
          1 - ((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p ≤ ((1270 / 100 : ℚ) : ℝ) * (p : ℝ) ^ (-(1 : ℝ) / 7) := by
  have hd := tabP1_data7
  obtain ⟨a, b, c, d, e⟩ := tabP1_of 7 (by norm_num) (1280189 / 250000) (5322 * 10 ^ 4) (1270 / 100) (2475 / 1000) (2485 / 1000) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hd.1, hd.2.1, a, b, c, d, fun p hp hPp => by have := e p hp hPp; exact_mod_cast this⟩

/-! ## `tab:LFY` (the thresholds `0.1` and `0.3` used by `thm:LF`(a)) -/

/-- **`F(u^*) < 1 - Y` gives `LB > Y`** (`app:LFdata`, `tab:LFY`): for every rational `u^* > u_min` with
`F(u^*) < 1 - Y` (`Y ≥ 0`) and every prime `p ≥ max(Q_s^s u^{*s}, s)`, the mixed-radix rule has `Γ < p` and
`(p - Γ)/p > Y`. -/
theorem MRall_Y (s : ℕ) (hs : 3 ≤ s) (us Y : ℚ) (hY : 0 ≤ Y) (hus : mrUmin s < us) (hF : mrF s us < 1 - Y)
    (p : ℕ) (hp : p.Prime) (hP : ((mrQss s * us ^ s : ℚ) : ℝ) ≤ p) (hsp : s ≤ p) :
    mrCost s p (mrRuleH s p) < p ∧ (Y : ℝ) < ((p : ℝ) - mrCost s p (mrRuleH s p)) / p := by
  have hFr : mrF s (us : ℝ) < 1 - Y := by
    rw [← mrF_cast s (by omega)]; exact_mod_cast hF
  have husr : (mrUmin s : ℝ) < us := by exact_mod_cast hus
  have ha0 : (0 : ℝ) ≤ mrUmin s := by exact_mod_cast (mrUmin_pos s (by omega)).le
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hvu : (us : ℝ) ≤ mrU s p :=
    (le_mrU_iff s p (by omega) hp1 (ha0.trans husr.le)).mpr (by push_cast at hP; exact hP)
  have hY' : (0 : ℝ) ≤ Y := by exact_mod_cast hY
  obtain ⟨hΓ, hb, -, -⟩ := mrall_core s p hs hp1 us husr (by linarith) hvu
  have hFu : mrF s (mrU s p) ≤ mrF s (us : ℝ) :=
    (mrF_mono s (by omega)).1.2 husr (lt_of_lt_of_le husr hvu) hvu
  refine ⟨hΓ, ?_⟩
  rw [sub_div, div_self hp0.ne']
  linarith

theorem tabLFY_data :
    (mrUmin 3 < (312163 / 10 ^ 5 : ℚ) ∧ mrF 3 (312163 / 10 ^ 5 : ℚ) < 1 - 1 / 10 ∧
      mrQss 3 * (312163 / 10 ^ 5 : ℚ) ^ 3 ≤ 7605 / 100) ∧
    (mrUmin 3 < (3628053 / 10 ^ 6 : ℚ) ∧ mrF 3 (3628053 / 10 ^ 6 : ℚ) < 1 - 3 / 10 ∧
      mrQss 3 * (3628053 / 10 ^ 6 : ℚ) ^ 3 ≤ 11939 / 100) ∧
    (mrUmin 4 < (46201 / 12500 : ℚ) ∧ mrF 4 (46201 / 12500 : ℚ) < 1 - 1 / 10 ∧
      mrQss 4 * (46201 / 12500 : ℚ) ^ 4 ≤ 111283 / 100) ∧
    (mrUmin 4 < (529641 / 125000 : ℚ) ∧ mrF 4 (529641 / 125000 : ℚ) < 1 - 3 / 10 ∧
      mrQss 4 * (529641 / 125000 : ℚ) ^ 4 ≤ 192198 / 100) ∧
    (mrUmin 5 < (667839 / 200000 : ℚ) ∧ mrF 5 (667839 / 200000 : ℚ) < 1 - 1 / 10 ∧
      mrQss 5 * (667839 / 200000 : ℚ) ^ 5 ≤ 1060949 / 100) ∧
    (mrUmin 5 < (1911393 / 500000 : ℚ) ∧ mrF 5 (1911393 / 500000 : ℚ) < 1 - 3 / 10 ∧
      mrQss 5 * (1911393 / 500000 : ℚ) ^ 5 ≤ 2086341 / 100) := by
  decide +kernel

/-- **`tab:LFY`**: the mixed-radix rule has `(p - Γ)/p > 0.1` for every prime `p ≥ 76.05`, `1112.83`, `10609.49`
and `(p - Γ)/p > 0.3` for every prime `p ≥ 119.39`, `1921.98`, `20863.41` (`s = 3, 4, 5`). -/
theorem tabLFY :
    (∀ p : ℕ, p.Prime → (7605 / 100 : ℝ) ≤ p →
      (1 / 10 : ℝ) < ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
    (∀ p : ℕ, p.Prime → (11939 / 100 : ℝ) ≤ p →
      (3 / 10 : ℝ) < ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
    (∀ p : ℕ, p.Prime → (111283 / 100 : ℝ) ≤ p →
      (1 / 10 : ℝ) < ((p : ℝ) - mrCost 4 p (mrRuleH 4 p)) / p) ∧
    (∀ p : ℕ, p.Prime → (192198 / 100 : ℝ) ≤ p →
      (3 / 10 : ℝ) < ((p : ℝ) - mrCost 4 p (mrRuleH 4 p)) / p) ∧
    (∀ p : ℕ, p.Prime → (1060949 / 100 : ℝ) ≤ p →
      (1 / 10 : ℝ) < ((p : ℝ) - mrCost 5 p (mrRuleH 5 p)) / p) ∧
    (∀ p : ℕ, p.Prime → (2086341 / 100 : ℝ) ≤ p →
      (3 / 10 : ℝ) < ((p : ℝ) - mrCost 5 p (mrRuleH 5 p)) / p) := by
  obtain ⟨⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩, ⟨a3, b3, c3⟩, ⟨a4, b4, c4⟩, ⟨a5, b5, c5⟩, ⟨a6, b6, c6⟩⟩ := tabLFY_data
  have key : ∀ (s : ℕ) (hs : 3 ≤ s) (us Y P : ℚ), 0 ≤ Y → (s : ℚ) ≤ P → mrUmin s < us → mrF s us < 1 - Y →
      mrQss s * us ^ s ≤ P → ∀ p : ℕ, p.Prime → (P : ℝ) ≤ p →
        (Y : ℝ) < ((p : ℝ) - mrCost s p (mrRuleH s p)) / p := by
    intro s hs us Y P hY hPs hu hF hP p hp hPp
    have hP' : ((mrQss s * us ^ s : ℚ) : ℝ) ≤ p := (by exact_mod_cast hP : ((mrQss s * us ^ s : ℚ) : ℝ) ≤ P).trans hPp
    have hsp : s ≤ p := by
      have : ((s : ℚ) : ℝ) ≤ P := by exact_mod_cast hPs
      have : (s : ℝ) ≤ p := by push_cast at this; linarith
      exact_mod_cast this
    exact (MRall_Y s hs us Y hY hu hF p hp hP' hsp).2
  refine ⟨fun p hp h => ?_, fun p hp h => ?_, fun p hp h => ?_, fun p hp h => ?_, fun p hp h => ?_,
    fun p hp h => ?_⟩
  · have := key 3 le_rfl _ (1 / 10) (7605 / 100) (by norm_num) (by norm_num) a1 b1 c1 p hp (by push_cast; linarith)
    push_cast at this; exact this
  · have := key 3 le_rfl _ (3 / 10) (11939 / 100) (by norm_num) (by norm_num) a2 b2 c2 p hp (by push_cast; linarith)
    push_cast at this; exact this
  · have := key 4 (by norm_num) _ (1 / 10) (111283 / 100) (by norm_num) (by norm_num) a3 b3 c3 p hp
      (by push_cast; linarith)
    push_cast at this; exact this
  · have := key 4 (by norm_num) _ (3 / 10) (192198 / 100) (by norm_num) (by norm_num) a4 b4 c4 p hp
      (by push_cast; linarith)
    push_cast at this; exact this
  · have := key 5 (by norm_num) _ (1 / 10) (1060949 / 100) (by norm_num) (by norm_num) a5 b5 c5 p hp
      (by push_cast; linarith)
    push_cast at this; exact this
  · have := key 5 (by norm_num) _ (3 / 10) (2086341 / 100) (by norm_num) (by norm_num) a6 b6 c6 p hp
      (by push_cast; linarith)
    push_cast at this; exact this

end GeoSeq
