/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Tab

@[expose] public section

/-!
# GeoSeq stage V3: the mixed-radix rule below `p_1(s)` for `s = 3, 4, 5` (last column of `tab:P1`)

A reflected checker: for every integer `n` of a range, either `n` has a divisor `2 ≤ d < min(n, B)` or the exact
step factors (`mrHqAux`, rational `s`-th powers) satisfy the rounding bracket — so they are the step factors
`h_t = max(1, round(γ_t u))` of the mixed-radix rule (`mrRuleH_eq_of_bracket`) — and `Γ < n`. Soundness
`mrRange_sound`; the three ranges `[41, 64)`, `[557, 890)`, `[6421, 8058)` are checked by `decide +kernel`
(each well under a second). With `tabP1_s3/4/5` above `P`: `MR_every_prime_s3/4/5` — the mixed-radix rule has
`Γ < p` for every prime `p ≥ 41`, `557`, `6421`. Also `MR_fail_s5`: it fails at `6397` (and works at `1693`,
`MR_works_1693`): the primes where it fails are not an initial segment.
-/

namespace GeoSeq

open Finset

/-! ## `mrCost` depends only on `h_1, …, h_n` -/

section Congr

variable {s p : ℕ} {h h' : ℕ → ℕ}

lemma mrNu_congr (hh : ∀ i, 1 ≤ i → i ≤ s - 1 → h i = h' i) (t j : ℕ) (hj : j < s) :
    mrNu s h t j = mrNu s h' t j := by
  unfold mrNu hprod
  congr 1
  exact prod_congr rfl fun i hi => hh i (by have := (mem_Ioc.mp hi).1; omega)
    (by have := (mem_Ioc.mp hi).2; omega)

lemma mrN_congr (hh : ∀ i, 1 ≤ i → i ≤ s - 1 → h i = h' i) (j : ℕ) (hj : j < s) (t : ℕ) :
    mrN s p h j t = mrN s p h' j t := by
  induction t with
  | zero => simp only [mrN, mrNu_congr hh 0 j hj]
  | succ t ih => simp only [mrN, ih, mrNu_congr hh (t + 1) j hj]

lemma mrCost_congr (hh : ∀ i, 1 ≤ i → i ≤ s - 1 → h i = h' i) : mrCost s p h = mrCost s p h' := by
  have hBx : ∀ t j, j < s → mrBx s p h t j = mrBx s p h' t j := fun t j hj => by
    simp only [mrBx, mrNu_congr hh _ j hj, mrN_congr hh j hj]
  have hB : ∀ c, mrB s p h c = mrB s p h' c := fun c => by
    unfold mrB; exact sum_congr rfl fun j hj => hBx c j (mem_Ioo.mp hj).2
  have hM : ∀ j, j < s → mrM s p h j = mrM s p h' j := fun j hj => by
    simp only [mrM, mrN_congr hh j hj]
  unfold mrCost
  exact Finset.sup_congr rfl fun c hc => by rw [hB c, hM c (mem_range.mp hc)]

end Congr

/-! ## The checker -/

/-- The rounding bracket of `k` for `γ_t u(p)` (rational `s`-th powers). -/
def mrBracket (s p t k : ℕ) : Bool :=
  if k = 0 then decide ((2 ^ s * mrGamma s t ^ s * p : ℚ) < mrQss s)
  else decide (((2 * k - 1 : ℚ)) ^ s * mrQss s ≤ 2 ^ s * mrGamma s t ^ s * p) &&
    decide ((2 ^ s * mrGamma s t ^ s * p : ℚ) < ((2 * k + 1 : ℚ)) ^ s * mrQss s)

/-- The exact rounding search (fuel `64`). -/
def mrHk (s p t : ℕ) : ℕ := mrHqAux s p t 64 0

/-- `n` passes: every bracket holds and `Γ < n` for the step factors `max(1, mrHk)`. -/
def mrOK (s n : ℕ) : Bool :=
  (List.range (s - 1)).all (fun i => mrBracket s n (i + 1) (mrHk s n (i + 1))) &&
    decide (mrCost s n (fun t => max 1 (mrHk s n t)) < n)

/-- A divisor `2 ≤ d < min(n, B)` of `n`. -/
def mrSmallDiv (n B : ℕ) : Bool := (List.range B).any (fun d => 2 ≤ d && d < n && n % d == 0)

/-- Every `n ∈ [a, a + len)` has a small divisor or passes `mrOK`. -/
def mrRangeOK (s a len B : ℕ) : Bool := (List.range len).all (fun i => mrSmallDiv (a + i) B || mrOK s (a + i))

lemma round_eq_zero_of_bracket (s p t : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) (ht1 : 1 ≤ t) (ht : t ≤ s - 1)
    (h0 : (2 ^ s * mrGamma s t ^ s * p : ℚ) < mrQss s) : mrRuleH s p t = 1 := by
  set x : ℝ := (mrGamma s t : ℝ) * mrU s p with hx
  have hγ : (0 : ℝ) < mrGamma s t := by exact_mod_cast mrGamma_pos s t hs ht1 ht
  have hx0 : 0 ≤ x := by have := mrU_pos s p hs hp; positivity
  have hQ := mrQss_pos_real s hs
  have hxs : (2 * x) ^ s * mrQss s = 2 ^ s * (mrGamma s t : ℝ) ^ s * p := by
    rw [hx, mul_pow, mul_pow, mul_assoc, mul_assoc, mul_comm (mrU s p ^ s), ← mrPu, mrPu_mrU s p hs]
    ring
  have h0' : (2 * x) ^ s * mrQss s < 1 ^ s * mrQss s := by rw [hxs, one_pow, one_mul]; exact_mod_cast h0
  have a2 : 2 * x < 1 :=
    (pow_lt_pow_iff_left₀ (by positivity) zero_le_one (by omega)).mp (lt_of_mul_lt_mul_right h0' hQ.le)
  have hr : round x = 0 := by
    rw [round_eq, Int.floor_eq_iff]; push_cast; constructor <;> linarith
  unfold mrRuleH
  rw [← hx, hr]
  rfl

lemma mrRuleH_of_bracket (s p t : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) (ht1 : 1 ≤ t) (ht : t ≤ s - 1) (k : ℕ)
    (hb : mrBracket s p t k = true) : mrRuleH s p t = max 1 k := by
  unfold mrBracket at hb
  split_ifs at hb with hk
  · subst hk; exact round_eq_zero_of_bracket s p t hs hp ht1 ht (of_decide_eq_true hb)
  · rw [Bool.and_eq_true] at hb
    rw [mrRuleH_eq_of_bracket s p hs hp t ht1 ht k (by omega) (of_decide_eq_true hb.1)
      (of_decide_eq_true hb.2)]
    omega

/-- **Soundness of the range checker**: if `mrRangeOK s a len B`, then the mixed-radix rule has `Γ < p` at
every prime `p ∈ [a, a + len)`. -/
theorem mrRange_sound (s a len B : ℕ) (hs : 2 ≤ s) (hok : mrRangeOK s a len B = true) (p : ℕ) (hp : p.Prime)
    (hap : a ≤ p) (hpl : p < a + len) : mrCost s p (mrRuleH s p) < p := by
  unfold mrRangeOK at hok
  have hi := List.all_eq_true.mp hok (p - a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_cancel' hap, Bool.or_eq_true] at hi
  rcases hi with hd | hm
  · exfalso
    obtain ⟨d, -, hd⟩ := List.any_eq_true.mp hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
    obtain ⟨⟨h2, hdp⟩, hmod⟩ := hd
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega
  · unfold mrOK at hm
    rw [Bool.and_eq_true] at hm
    obtain ⟨hb, hc⟩ := hm
    have hp1 : 1 ≤ p := hp.one_lt.le
    rw [mrCost_congr (h' := fun t => max 1 (mrHk s p t)) fun i h1 h2 =>
      mrRuleH_of_bracket s p i hs hp1 h1 h2 _ (List.all_eq_true.mp hb (i - 1)
        (List.mem_range.mpr (by omega)) |> fun h => by rwa [Nat.sub_add_cancel h1] at h)]
    exact of_decide_eq_true hc

theorem mrRange3 : mrRangeOK 3 41 23 10 = true := by decide +kernel
theorem mrRange4 : mrRangeOK 4 557 333 31 = true := by decide +kernel
theorem mrRange5 : mrRangeOK 5 6421 1637 92 = true := by decide +kernel

lemma mrRuleH_cost (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p)
    (hb : (List.range (s - 1)).all (fun i => mrBracket s p (i + 1) (mrHk s p (i + 1))) = true) :
    mrCost s p (mrRuleH s p) = mrCost s p (fun t => max 1 (mrHk s p t)) :=
  mrCost_congr fun i h1 h2 => mrRuleH_of_bracket s p i hs hp h1 h2 _ (List.all_eq_true.mp hb (i - 1)
    (List.mem_range.mpr (by omega)) |> fun h => by rwa [Nat.sub_add_cancel h1] at h)

/-- **The last column of `tab:P1`, `s = 3`**: the mixed-radix rule has `Γ < p` for every prime `p ≥ 41`
(`[41, 63]` by the range checker, `p ≥ 64 > 63.18` by `tabP1_s3`). -/
theorem MR_every_prime_s3 (p : ℕ) (hp : p.Prime) (h41 : 41 ≤ p) : mrCost 3 p (mrRuleH 3 p) < p := by
  by_cases hlt : p < 64
  · exact mrRange_sound 3 41 23 10 (by norm_num) mrRange3 p hp h41 (by omega)
  · refine (tabP1_s3.2.2.2.2.2.2 p hp ?_).1
    have : (64 : ℝ) ≤ p := by exact_mod_cast (by omega : 64 ≤ p)
    push_cast; linarith

/-- **The last column of `tab:P1`, `s = 4`**: `Γ < p` for every prime `p ≥ 557` (`[557, 889]` by the range
checker, `p ≥ 890 > 889.9` by `tabP1_s4`). -/
theorem MR_every_prime_s4 (p : ℕ) (hp : p.Prime) (h557 : 557 ≤ p) : mrCost 4 p (mrRuleH 4 p) < p := by
  by_cases hlt : p < 890
  · exact mrRange_sound 4 557 333 31 (by norm_num) mrRange4 p hp h557 (by omega)
  · refine (tabP1_s4.2.2.2.2.2.2 p hp ?_).1
    have : (890 : ℝ) ≤ p := by exact_mod_cast (by omega : 890 ≤ p)
    push_cast; linarith

/-- **The last column of `tab:P1`, `s = 5`**: `Γ < p` for every prime `p ≥ 6421` (`[6421, 8057]` by the range
checker, `p ≥ 8058 > 8057.9` by `tabP1_s5`). -/
theorem MR_every_prime_s5 (p : ℕ) (hp : p.Prime) (h6421 : 6421 ≤ p) : mrCost 5 p (mrRuleH 5 p) < p := by
  by_cases hlt : p < 8058
  · exact mrRange_sound 5 6421 1637 92 (by norm_num) mrRange5 p hp h6421 (by omega)
  · refine (tabP1_s5.2.2.2.2.2.2 p hp ?_).1
    have : (8058 : ℝ) ≤ p := by exact_mod_cast (by omega : 8058 ≤ p)
    push_cast; linarith

/-- The thresholds `41`, `557`, `6421` are the primes from which the rule works (it fails at the primes `37`,
`547`, `6397` just below them), and for `s = 5` the failures are not an initial segment (it works at `1693`;
the remark after `tab:P1`). -/
theorem MR_sharp :
    37 ≤ mrCost 3 37 (mrRuleH 3 37) ∧ 547 ≤ mrCost 4 547 (mrRuleH 4 547) ∧
      6397 ≤ mrCost 5 6397 (mrRuleH 5 6397) ∧ mrCost 5 1693 (mrRuleH 5 1693) < 1693 := by
  rw [mrRuleH_cost 3 37 (by norm_num) (by norm_num) (by decide +kernel),
    mrRuleH_cost 4 547 (by norm_num) (by norm_num) (by decide +kernel),
    mrRuleH_cost 5 6397 (by norm_num) (by norm_num) (by decide +kernel),
    mrRuleH_cost 5 1693 (by norm_num) (by norm_num) (by decide +kernel)]
  decide +kernel

end GeoSeq
