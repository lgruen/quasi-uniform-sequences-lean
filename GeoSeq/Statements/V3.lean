/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Defs

@[expose] public section

/-!
# Statements: stage V3 (every dimension: `lem:MRbound`, `thm:MRall`, `tab:P1`, `tab:LFY`; `prop:lexcap`,
  `prop:lexmin`, `prop:tournament`)

PROVED (`GeoSeq/V3Mono.lean`, `GeoSeq/V3Bound.lean`, `GeoSeq/V3.lean`, `GeoSeq/V3Tab.lean`, `GeoSeq/V3Range.lean`,
`GeoSeq/V3Cap.lean`, `GeoSeq/V3Lexmin.lean`, `GeoSeq/V3Tour.lean`, `GeoSeq/V3Ex.lean`); generated verbatim from the proof files' signatures (definitions in `GeoSeq/V3Defs.lean`).
Paper: V3 (development version V3 of the paper, `05-order.tex`, `A-machinery.tex`, `E-designs.tex`); label → Lean map in
the formalization notes of the research repository, review the statement-review notes of the research repository.

* `lem:MRbound`: `mr_bound_u` (real `u`), `MRbound` (at `u = p^{1/s}/Q_s`), `MRbound_mono`; the extra hypothesis
  `F_0(u) ≤ 1` is discussed in the review.
* the mixed-radix rule: `mrPu_mrU`, `mrRuleH_bound`, `mr_no_ties`, `mrRuleH_eq_of_bracket`.
* **`thm:MRall`**: `MRall_a`, `MRall_b`, `MRall_c`; rational certificates `mrF_cast`, `MRall_rat`, `MRall_Y`.
* `tab:P1`: `tabP1_s3` … `tabP1_s7` (`decide +kernel`); last column `MR_every_prime_s3/4/5` (range checker,
  `decide +kernel`), `MR_sharp`; `tab:LFY`: `tabLFY`.
* `prop:lexcap`: `lexcap`; `MR_cap` (the mixed-radix rule attains the rate `p^{-1/s}`).
* `prop:lexmin`: `lexmin` (any order of the coordinates; helpers `winLB_perm`, `kapL_ne_zero`, the finite check
  `lexmin_check7`).
* `prop:tournament`: `tournament`, `tournament_card`, `tournament_min`.
* non-vacuity: `MRall_example` (`s = 3`, `p = 67`).
-/

namespace GeoSeq
open Finset PowerSeries

section Bound
variable (s p : ℕ) (h : ℕ → ℕ) (u : ℝ)

/-- **`lem:MRbound`, first part** (real parameter `u`): if `u > u_min`, `p = Q_s^s u^s` (`p ≥ 1`), the step
factors satisfy `|h_t - γ_t u| ≤ 1/2` (`1 ≤ t ≤ n`) and `F_0(u) ≤ 1`, then `Γ/p ≤ F(u)`. -/
theorem mr_bound_u (hs : 2 ≤ s) (hp : 1 ≤ p) (hu : (mrUmin s : ℝ) < u) (hpu : (p : ℝ) = mrPu s u)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → |(h t : ℝ) - mrGamma s t * u| ≤ 1 / 2)
    (hF0 : mrFrow s 0 u ≤ 1) :
    (mrCost s p h : ℝ) / p ≤ mrF s u := by
  sorry

end Bound

/-- `p = Q_s^s u(p)^s`. -/
theorem mrPu_mrU (s p : ℕ) (hs : 2 ≤ s) : mrPu s (mrU s p) = p := by
  sorry

/-- **`lem:MRbound`, first part.** Let `s ≥ 3`, `p ≥ 1` (the paper: `p ≥ s` prime) with
`u = p^{1/s}/Q_s > u_min`, and let the step factors satisfy `|h_t - γ_t u| ≤ 1/2` (`1 ≤ t ≤ n`, as in the
mixed-radix rule). If moreover `F_0(u) ≤ 1` (the row-`0` bound; it holds whenever `F(u) ≤ 1`, in particular
in every application in `thm:MRall`), then `Γ/p ≤ F(u)`. -/
theorem MRbound (s p : ℕ) (hs : 3 ≤ s) (hp : 1 ≤ p) (h : ℕ → ℕ) (hu : (mrUmin s : ℝ) < mrU s p)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → |(h t : ℝ) - mrGamma s t * mrU s p| ≤ 1 / 2)
    (hF0 : mrFrow s 0 (mrU s p) ≤ 1) :
    (mrCost s p h : ℝ) / p ≤ mrF s (mrU s p) := by
  sorry

/-- **`lem:MRbound`, second part**: `F` and `u ↦ u F(u)` are non-increasing on `(u_min, ∞)` (and `F ≥ 0`
there), every `s ≥ 3`. -/
theorem MRbound_mono (s : ℕ) (hs : 3 ≤ s) :
    AntitoneOn (fun u => mrF s u) (Set.Ioi (mrUmin s : ℝ)) ∧
      AntitoneOn (fun u => u * mrF s u) (Set.Ioi (mrUmin s : ℝ)) ∧
      ∀ u : ℝ, (mrUmin s : ℝ) < u → 0 ≤ mrF s u := by
  sorry

/-- The step factors of the mixed-radix rule satisfy `|h_t - γ_t u| ≤ 1/2` once `u > u_min`. -/
theorem mrRuleH_bound (s p : ℕ) (hs : 2 ≤ s) (hu : (mrUmin s : ℝ) < mrU s p) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t ≤ s - 1) : |(mrRuleH s p t : ℝ) - mrGamma s t * mrU s p| ≤ 1 / 2 := by
  sorry

/-- **No ties** in the rounding of the mixed-radix rule: if `p` is prime and `v_p(Q_s^s/γ_t^s) = 0` (all but
finitely many primes), then `γ_t u(p)` is not of the form `k + 1/2`; so `round(γ_t u)` does not depend on the
rounding convention. -/
theorem mr_no_ties (s p : ℕ) [hp : Fact p.Prime] (hs : 2 ≤ s) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ s - 1)
    (hv : padicValRat p (mrQss s / mrGamma s t ^ s) = 0) (k : ℤ) :
    (mrGamma s t : ℝ) * mrU s p ≠ k + 1 / 2 := by
  sorry

/-- **Exact rational form of the rounding**: if `k ≥ 1` and `(2k-1)^s Q_s^s ≤ 2^s γ_t^s p < (2k+1)^s Q_s^s`,
then the mixed-radix rule takes `h_t = k`. -/
theorem mrRuleH_eq_of_bracket (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ s - 1)
    (k : ℕ) (hk : 1 ≤ k)
    (h1 : ((2 * k - 1 : ℚ)) ^ s * mrQss s ≤ 2 ^ s * mrGamma s t ^ s * p)
    (h2 : 2 ^ s * mrGamma s t ^ s * p < ((2 * k + 1 : ℚ)) ^ s * mrQss s) :
    mrRuleH s p t = k := by
  sorry

/-- **`thm:MRall`(a)**: `p_1(s)` is finite. With `u_0 = 2u_min` and `u_b = max(u_0, 2u_0 F(u_0))`: `F(u_b) ≤ 1/2`,
so the set `{u > u_min : F(u) < 1}` is nonempty, `u_min ≤ u_1(s) ≤ u_b` and `p_1(s) ≤ Q_s^s u_b^s`. -/
theorem MRall_a (s : ℕ) (hs : 3 ≤ s) :
    (mrUmin s : ℝ) < max (2 * (mrUmin s : ℝ)) (2 * (2 * (mrUmin s : ℝ)) * mrF s (2 * (mrUmin s : ℝ))) ∧
    mrF s (max (2 * (mrUmin s : ℝ)) (2 * (2 * (mrUmin s : ℝ)) * mrF s (2 * (mrUmin s : ℝ)))) ≤ 1 / 2 ∧
    {u : ℝ | (mrUmin s : ℝ) < u ∧ mrF s u < 1}.Nonempty ∧
    (mrUmin s : ℝ) ≤ mrU1 s ∧
    mrU1 s ≤ max (2 * (mrUmin s : ℝ)) (2 * (2 * (mrUmin s : ℝ)) * mrF s (2 * (mrUmin s : ℝ))) ∧
    mrP1 s ≤ (mrQss s : ℝ) *
      (max (2 * (mrUmin s : ℝ)) (2 * (2 * (mrUmin s : ℝ)) * mrF s (2 * (mrUmin s : ℝ)))) ^ s := by
  sorry

/-- **`thm:MRall`(b)**: for every prime `p > max(p_1(s), s)` the mixed-radix rule has `Γ < p`; so (`thm:MR`)
for every choice of the local roots of the Faure frame a selection rule exists, and every selection rule gives a
quasi-uniform digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem MRall_b (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hp1 : mrP1 s < p) (hsp : s < p) :
    mrCost s p (mrRuleH s p) < p ∧
    ∀ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (faureW s p) = C (mrTheta s p) * X) →
      (∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) →
      (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (mrTheta s p) (mrLam s p (mrRuleH s p)) zθ (mrWin s p (mrRuleH s p)) rule) ∧
      ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (mrTheta s p) (mrLam s p (mrRuleH s p)) zθ (mrWin s p (mrRuleH s p)) rule →
        IsSeq0 (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p (mrRuleH s p)) zθ rule) zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
          (seqPoint (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p (mrRuleH s p)) zθ rule) zθ))
          (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist
              (prefixSet N (seqPoint (zcode p)
                (ssGen (ruleMult (mrTheta s p) (mrLam s p (mrRuleH s p)) zθ rule) zθ))) ≤
            Real.sqrt s * p / (((p : ℝ) - mrCost s p (mrRuleH s p)) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
                (prefixSet N (seqPoint (zcode p)
                  (ssGen (ruleMult (mrTheta s p) (mrLam s p (mrRuleH s p)) zθ rule) zθ)))) := by
  sorry

/-- **`thm:MRall`(c)**: for every real (in particular every rational) `u^* > u_min` with `F(u^*) < 1` and every
prime `p ≥ max(Q_s^s u^{*s}, s)`, the mixed-radix rule has `Γ < p` and
`1 - (p - Γ)/p = Γ/p ≤ C'_s p^{-1/s}` with `C'_s = Q_s u^* F(u^*)`. -/
theorem MRall_c (s p : ℕ) [hpr : Fact p.Prime] (hs : 3 ≤ s) (us : ℝ) (hus : (mrUmin s : ℝ) < us)
    (hF : mrF s us < 1) (hp : (mrQss s : ℝ) * us ^ s ≤ p) (hsp : s ≤ p) :
    mrCost s p (mrRuleH s p) < p ∧
      1 - ((p : ℝ) - mrCost s p (mrRuleH s p)) / p = (mrCost s p (mrRuleH s p) : ℝ) / p ∧
      (mrCost s p (mrRuleH s p) : ℝ) / p ≤ mrCp s us * (p : ℝ) ^ (-(1 : ℝ) / s) := by
  sorry

/-- `F` at a rational point is the rational `F` (exact evaluation of `tab:P1`, `tab:LFY`). -/
theorem mrF_cast (s : ℕ) (hs : 1 ≤ s) (q : ℚ) : ((mrF s q : ℚ) : ℝ) = mrF s (q : ℝ) := by
  sorry

/-- **Rational certificates** (the remark after `thm:MRall`, `tab:P1`): if a rational `u^* > u_min` has
`F(u^*) < 1`, `Q_s^s u^{*s} ≤ P` and `Q_s^s (u^* F(u^*))^s ≤ C^s` (`C ≥ 0`; all exact rational inequalities), then
`p_1(s) ≤ P`, `C'_s = Q_s u^* F(u^*) ≤ C`, and for every prime `p ≥ max(P, s)` the mixed-radix rule has `Γ < p`
and `1 - (p - Γ)/p ≤ C p^{-1/s}`. -/
theorem MRall_rat (s : ℕ) (hs : 3 ≤ s) (us P C : ℚ) (hus : mrUmin s < us) (hF : mrF s us < 1)
    (hP : mrQss s * us ^ s ≤ P) (hC0 : 0 ≤ C) (hC : mrQss s * (us * mrF s us) ^ s ≤ C ^ s) :
    mrP1 s ≤ P ∧ mrCp s us ≤ C ∧
      ∀ p : ℕ, p.Prime → (P : ℝ) ≤ p → s ≤ p →
        mrCost s p (mrRuleH s p) < p ∧
          1 - ((p : ℝ) - mrCost s p (mrRuleH s p)) / p ≤ C * (p : ℝ) ^ (-(1 : ℝ) / s) := by
  sorry

/-- **`F(u^*) < 1 - Y` gives `LB > Y`** (`app:LFdata`, `tab:LFY`): for every rational `u^* > u_min` with
`F(u^*) < 1 - Y` (`Y ≥ 0`) and every prime `p ≥ max(Q_s^s u^{*s}, s)`, the mixed-radix rule has `Γ < p` and
`(p - Γ)/p > Y`. -/
theorem MRall_Y (s : ℕ) (hs : 3 ≤ s) (us Y : ℚ) (hY : 0 ≤ Y) (hus : mrUmin s < us) (hF : mrF s us < 1 - Y)
    (p : ℕ) (hp : p.Prime) (hP : ((mrQss s * us ^ s : ℚ) : ℝ) ≤ p) (hsp : s ≤ p) :
    mrCost s p (mrRuleH s p) < p ∧ (Y : ℝ) < ((p : ℝ) - mrCost s p (mrRuleH s p)) / p := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **The last column of `tab:P1`, `s = 3`**: the mixed-radix rule has `Γ < p` for every prime `p ≥ 41`
(`[41, 63]` by the range checker, `p ≥ 64 > 63.18` by `tabP1_s3`). -/
theorem MR_every_prime_s3 (p : ℕ) (hp : p.Prime) (h41 : 41 ≤ p) : mrCost 3 p (mrRuleH 3 p) < p := by
  sorry

/-- **The last column of `tab:P1`, `s = 4`**: `Γ < p` for every prime `p ≥ 557` (`[557, 889]` by the range
checker, `p ≥ 890 > 889.9` by `tabP1_s4`). -/
theorem MR_every_prime_s4 (p : ℕ) (hp : p.Prime) (h557 : 557 ≤ p) : mrCost 4 p (mrRuleH 4 p) < p := by
  sorry

/-- **The last column of `tab:P1`, `s = 5`**: `Γ < p` for every prime `p ≥ 6421` (`[6421, 8057]` by the range
checker, `p ≥ 8058 > 8057.9` by `tabP1_s5`). -/
theorem MR_every_prime_s5 (p : ℕ) (hp : p.Prime) (h6421 : 6421 ≤ p) : mrCost 5 p (mrRuleH 5 p) < p := by
  sorry

/-- The thresholds `41`, `557`, `6421` are the primes from which the rule works (it fails at the primes `37`,
`547`, `6397` just below them), and for `s = 5` the failures are not an initial segment (it works at `1693`;
the remark after `tab:P1`). -/
theorem MR_sharp :
    37 ≤ mrCost 3 37 (mrRuleH 3 37) ∧ 547 ≤ mrCost 4 547 (mrRuleH 4 547) ∧
      6397 ≤ mrCost 5 6397 (mrRuleH 5 6397) ∧ mrCost 5 1693 (mrRuleH 5 1693) < 1693 := by
  sorry


section Cap
variable {p : ℕ} [hp : Fact p.Prime]

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
  sorry

end Cap

/-- **The mixed-radix rule attains the rate** (after `prop:lexcap`): `MR(s,p,h)` with `Γ < p` lies in the class
of `prop:lexcap`, so `1 - (p - Γ)/p ≥ p^{-1/s}` (`s = n + 1 ≥ 2`, `p ≥ s` prime, `h_t ≥ 1`); with `MRall_c`,
`p^{-1/s} ≤ 1 - LB(W) ≤ C'_s p^{-1/s}` for the mixed-radix rule. -/
theorem MR_cap (n p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (hsp : n + 1 ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ n + 1 - 1 → 1 ≤ h t) (hΓ : mrCost (n + 1) p h < p) :
    (p : ℝ) ^ (-(1 : ℝ) / (n + 1)) ≤ 1 - ((p : ℝ) - mrCost (n + 1) p h) / p := by
  sorry

/-- `WinLB` is invariant under relabelling the coordinates. -/
theorem winLB_perm {s p : ℕ} [NeZero p] (W : Fin s → Fin s → Set (ZMod p)) (π : Equiv.Perm (Fin s))
    (LB : ℝ) (h : WinLB p W LB) : WinLB p (fun i j => W (π i) (π j)) LB := by
  sorry

/-- The depth-zero crosses of a frame of distinct places with `θ ≠ 0`, `λ_c ≠ 0` are nonzero. -/
theorem kapL_ne_zero {F : Type*} [Field F] {s : ℕ} (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (hθ : θ ≠ 0) (hlam : ∀ c, lamv c ≠ 0) (c c' : Fin s)
    (hcc : c ≠ c') : kapL θ lamv zθ c c' ≠ 0 := by
  sorry

/-- The finite check of `prop:lexmin` at `p = 7` (`decide +kernel`): if `κ = ∓1` (`z = -κ ∈ {-1, 0, 1}`,
`κ ≠ 0`), then for every `A_1 ≤ 6` some `β_0` is missed by every line of column `1` whose own value runs over
`M_1 ≤ 4` consecutive values `[-A_1-3, -A_1]` (with `β_1 = 0`) and whose row-`0` value must land in `[-1, 1]`. -/
theorem lexmin_check7 : ∀ κ : ZMod 7, ∀ z ∈ Finset.Icc (-1 : ℤ) 1, (z : ZMod 7) = -κ → κ ≠ 0 →
    ∀ a ∈ Finset.range 7, ∃ β0 : ZMod 7, ∀ t : ZMod 7, ∀ z2 ∈ Finset.Icc (-(a : ℤ) - 3) (-(a : ℤ)),
      (z2 : ZMod 7) = 0 + t * 1 → ∀ z1 ∈ Finset.Icc (-1 : ℤ) 1, (z1 : ZMod 7) ≠ β0 + t * κ := by
  sorry

/-- **`prop:lexmin`** (minimum for ordered windows). For `s = 3` and `p ∈ {5, 7}`: let `W` be an ordered window
system (`def:lex`, data `A`, `M`, `B` with `IsLexData`) in the order `π` of the coordinates
(`W_{π i ← π j} = lexWin … i j`), over a frame of distinct places with `θ ≠ 0` and `λ_c ≠ 0`, satisfying
(i) (`-κ_{c←c'} ∈ W_{c←c'}`) and (ii) (every column covers) of `prop:steer`. Then no `LB > 0` satisfies
`WinLB p W LB`: `LB(W) ≤ 0`. -/
theorem lexmin (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7) (π : Equiv.Perm (Fin 3))
    (A M : Fin 3 → ℕ) (Bx : Fin 3 → Fin 3 → ℕ) (hd : IsLexData p A M Bx)
    (W : Fin 3 → Fin 3 → Set (ZMod p)) (hW : ∀ i j, W (π i) (π j) = lexWin p A M Bx i j)
    (θ : ZMod p) (lamv : Fin 3 → ZMod p) (zθ : Fin 3 → PowerSeries (ZMod p))
    (hinj : Function.Injective (ssPlace zθ)) (hθ : θ ≠ 0) (hlam : ∀ c, lamv c ≠ 0)
    (hi : ∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ W c c')
    (hii : ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    ¬ ∃ LB : ℝ, 0 < LB ∧ WinLB p W LB := by
  sorry

section Tournament
variable {s : ℕ}

/-- **`prop:tournament`**, first part: if every nonempty set `E` of coordinates has an element `c` with
`R c c'` for all other `c' ∈ E`, then in some order `v` of the coordinates every upper cross is restricted:
`R (v i) (v j)` for all `i < j`. -/
theorem tournament (R : Fin s → Fin s → Prop)
    (hR : ∀ E : Finset (Fin s), E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') :
    ∃ v : Fin s ≃ Fin s, ∀ i j : Fin s, i < j → R (v i) (v j) := by
  sorry

/-- **`prop:tournament`**: at least `s(s-1)/2` crosses are restricted. -/
theorem tournament_card (R : Fin s → Fin s → Prop) [DecidableRel R]
    (hR : ∀ E : Finset (Fin s), E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') :
    s * (s - 1) / 2 ≤ (univ.filter (fun x : Fin s × Fin s => x.1 ≠ x.2 ∧ R x.1 x.2)).card := by
  sorry

/-- **`prop:tournament`**, last sentence: the patterns with the property and exactly `s(s-1)/2` restricted
crosses are exactly the ordered patterns: `R c c' ⟺ v⁻¹ c < v⁻¹ c'` (`c ≠ c'`) for an order `v`. -/
theorem tournament_min (R : Fin s → Fin s → Prop) [DecidableRel R] :
    ((∀ E : Finset (Fin s), E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') ∧
        (univ.filter (fun x : Fin s × Fin s => x.1 ≠ x.2 ∧ R x.1 x.2)).card = s * (s - 1) / 2) ↔
      ∃ v : Fin s ≃ Fin s, ∀ c c' : Fin s, c ≠ c' → (R c c' ↔ v.symm c < v.symm c') := by
  sorry

end Tournament

/-- **Non-vacuity of `thm:MRall`(b)** at `s = 3`, `p = 67`. -/
theorem MRall_example :
    mrP1 3 < 67 ∧ mrCost 3 67 (mrRuleH 3 67) < 67 ∧
    (∃ zθ : Fin 3 → PowerSeries (ZMod 67),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 67) = C (mrTheta 3 67) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 67)) ∧
    ∀ zθ : Fin 3 → PowerSeries (ZMod 67),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 67) = C (mrTheta 3 67) * X) →
      (∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 67)) →
      (∃ rule : Fin 3 → ℕ → (ℕ → ZMod 67) → ZMod 67,
        IsSelRule (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ (mrWin 3 67 (mrRuleH 3 67)) rule) ∧
      ∀ rule : Fin 3 → ℕ → (ℕ → ZMod 67) → ZMod 67,
        IsSelRule (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ (mrWin 3 67 (mrRuleH 3 67)) rule →
        IsSeq0 (zcode 67) (ssGen (ruleMult (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ rule) zθ) ∧
        ∀ K : ℕ, 1 ≤ K → SepAtLevel 67 3 K
          (seqPoint (zcode 67) (ssGen (ruleMult (mrTheta 3 67) (mrLam 3 67 (mrRuleH 3 67)) zθ rule) zθ))
          (((67 : ℝ) - mrCost 3 67 (mrRuleH 3 67)) / 67) := by
  sorry


end GeoSeq
