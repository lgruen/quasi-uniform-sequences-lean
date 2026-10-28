/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Bound

@[expose] public section

/-!
# GeoSeq stage V3: every dimension (`lem:MRbound`, `thm:MRall`)

* `MRbound` (`lem:MRbound`, first part, at `u = p^{1/s}/Q_s`; hypothesis `F_0(u) ≤ 1`, see `mr_bound_u`) and
  `MRbound_mono` (second part: `F` and `u F(u)` are non-increasing on `(u_min, ∞)`), every `s ≥ 3`.
* the mixed-radix rule: `mrRuleH_bound` (`|h_t - γ_t u| ≤ 1/2` for `u > u_min`), `mr_no_ties` (`γ_t u` is never
  a half-integer at a prime `p` with `v_p(Q_s^s/γ_t^s) = 0`: `round` is unambiguous there),
  `mrRuleH_eq_of_bracket` (exact rational form of the rounding).
* **`MRall_a`**, **`MRall_b`**, **`MRall_c`** = `thm:MRall` (a), (b), (c) for every `s ≥ 3`.
* `MRall_rat` (the remark after `thm:MRall`): a rational `u^*` with `F(u^*) < 1` certifies `p_1(s) ≤ P`,
  `C'_s ≤ C` and the bound `Γ/p ≤ C p^{-1/s}` for every prime `p ≥ P` from the exact rational inequalities
  `Q_s^s u^{*s} ≤ P`, `Q_s^s (u^* F(u^*))^s ≤ C^s`; `mrF_cast` (`F` at a rational point is the rational `F`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## `Q_s`, `u(p)` -/

lemma mrQss_pos_real (s : ℕ) (hs : 2 ≤ s) : (0 : ℝ) < mrQss s := by exact_mod_cast mrQss_pos s hs

lemma mrQ_pos (s : ℕ) (hs : 2 ≤ s) : 0 < mrQ s := Real.rpow_pos_of_pos (mrQss_pos_real s hs) _

lemma mrQ_pow (s : ℕ) (hs : 2 ≤ s) : mrQ s ^ s = mrQss s := by
  unfold mrQ
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (mrQss_pos_real s hs).le (by omega)

lemma mrU_pos (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) : 0 < mrU s p := by
  unfold mrU
  have : (0 : ℝ) < p := by exact_mod_cast hp
  exact div_pos (Real.rpow_pos_of_pos this _) (mrQ_pos s hs)

/-- `p = Q_s^s u(p)^s`. -/
theorem mrPu_mrU (s p : ℕ) (hs : 2 ≤ s) : mrPu s (mrU s p) = p := by
  unfold mrPu mrU
  rw [div_pow, mrQ_pow s hs, one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)]
  field_simp [(mrQss_pos_real s hs).ne']

/-- `v ≤ u(p) ⟺ Q_s^s v^s ≤ p` for `v ≥ 0`. -/
lemma le_mrU_iff (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) {v : ℝ} (hv : 0 ≤ v) :
    v ≤ mrU s p ↔ (mrQss s : ℝ) * v ^ s ≤ p := by
  rw [← mrPu_mrU s p hs]
  unfold mrPu
  rw [mul_le_mul_iff_right₀ (mrQss_pos_real s hs),
    pow_le_pow_iff_left₀ hv (mrU_pos s p hs hp).le (by omega)]

/-- `v < u(p) ⟺ Q_s^s v^s < p` for `v ≥ 0`. -/
lemma lt_mrU_iff (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) {v : ℝ} (hv : 0 ≤ v) :
    v < mrU s p ↔ (mrQss s : ℝ) * v ^ s < p := by
  rw [← mrPu_mrU s p hs]
  unfold mrPu
  rw [mul_lt_mul_iff_right₀ (mrQss_pos_real s hs),
    pow_lt_pow_iff_left₀ hv (mrU_pos s p hs hp).le (by omega)]

/-! ## `lem:MRbound` -/

/-- **`lem:MRbound`, first part.** Let `s ≥ 3`, `p ≥ 1` (the paper: `p ≥ s` prime) with
`u = p^{1/s}/Q_s > u_min`, and let the step factors satisfy `|h_t - γ_t u| ≤ 1/2` (`1 ≤ t ≤ n`, as in the
mixed-radix rule). If moreover `F_0(u) ≤ 1` (the row-`0` bound; it holds whenever `F(u) ≤ 1`, in particular
in every application in `thm:MRall`), then `Γ/p ≤ F(u)`. -/
theorem MRbound (s p : ℕ) (hs : 3 ≤ s) (hp : 1 ≤ p) (h : ℕ → ℕ) (hu : (mrUmin s : ℝ) < mrU s p)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → |(h t : ℝ) - mrGamma s t * mrU s p| ≤ 1 / 2)
    (hF0 : mrFrow s 0 (mrU s p) ≤ 1) :
    (mrCost s p h : ℝ) / p ≤ mrF s (mrU s p) :=
  mr_bound_u s p h (mrU s p) (by omega) hp hu (mrPu_mrU s p (by omega)).symm hh hF0

/-- **`lem:MRbound`, second part**: `F` and `u ↦ u F(u)` are non-increasing on `(u_min, ∞)` (and `F ≥ 0`
there), every `s ≥ 3`. -/
theorem MRbound_mono (s : ℕ) (hs : 3 ≤ s) :
    AntitoneOn (fun u => mrF s u) (Set.Ioi (mrUmin s : ℝ)) ∧
      AntitoneOn (fun u => u * mrF s u) (Set.Ioi (mrUmin s : ℝ)) ∧
      ∀ u : ℝ, (mrUmin s : ℝ) < u → 0 ≤ mrF s u :=
  ⟨(mrF_mono s (by omega)).1.2, (mrF_mono s (by omega)).2, (mrF_mono s (by omega)).1.1⟩

lemma mrFrow0_le_mrF (s : ℕ) (hs : 1 ≤ s) (u : ℝ) : mrFrow s 0 u ≤ mrF s u := by
  have hne : (range s).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  unfold mrF
  rw [dite_eq_left_of_eq_true (eq_true hne)]
  exact Finset.le_sup' (fun c => mrFrow s c u) (mem_range.mpr (by omega))

/-! ## The mixed-radix rule -/

/-- The step factors of the mixed-radix rule satisfy `|h_t - γ_t u| ≤ 1/2` once `u > u_min`. -/
theorem mrRuleH_bound (s p : ℕ) (hs : 2 ≤ s) (hu : (mrUmin s : ℝ) < mrU s p) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t ≤ s - 1) : |(mrRuleH s p t : ℝ) - mrGamma s t * mrU s p| ≤ 1 / 2 := by
  set x : ℝ := (mrGamma s t : ℝ) * mrU s p with hx
  have hx2 : 1 / 2 < x := by
    have h1 := mrGamma_umin s t hs ht1 ht
    have h2 : (0 : ℝ) < mrGamma s t := by exact_mod_cast mrGamma_pos s t hs ht1 ht
    rw [hx]; nlinarith
  have hr : 1 ≤ round x := by
    rw [round_eq]; exact Int.le_floor.mpr (by push_cast; linarith)
  have hcast : (mrRuleH s p t : ℝ) = (round x : ℝ) := by
    unfold mrRuleH
    rw [← hx, max_eq_right (by omega)]
    have : (((round x).toNat : ℤ) : ℝ) = (round x : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
    rw [← this]; norm_cast
  rw [hcast, abs_sub_comm]
  exact abs_sub_round x

/-- **No ties** in the rounding of the mixed-radix rule: if `p` is prime and `v_p(Q_s^s/γ_t^s) = 0` (all but
finitely many primes), then `γ_t u(p)` is not of the form `k + 1/2`; so `round(γ_t u)` does not depend on the
rounding convention. -/
theorem mr_no_ties (s p : ℕ) [hp : Fact p.Prime] (hs : 2 ≤ s) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ s - 1)
    (hv : padicValRat p (mrQss s / mrGamma s t ^ s) = 0) (k : ℤ) :
    (mrGamma s t : ℝ) * mrU s p ≠ k + 1 / 2 := by
  intro heq
  have hγ : (0 : ℚ) < mrGamma s t := mrGamma_pos s t hs ht1 ht
  have hQ := mrQss_pos s hs
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  -- `γ^s p = (k + 1/2)^s Q^s` in `ℝ`, hence in `ℚ`
  have hreal : ((mrGamma s t ^ s * p : ℚ) : ℝ) = (((2 * k + 1) / 2) ^ s * mrQss s : ℚ) := by
    have e1 : ((mrGamma s t : ℝ) * mrU s p) ^ s * mrQss s = (mrGamma s t : ℝ) ^ s * p := by
      rw [mul_pow, mul_assoc, mul_comm (mrU s p ^ s), ← mrPu, mrPu_mrU s p hs]
    have e2 : ((k : ℝ) + 1 / 2) = (((2 * k + 1) / 2 : ℚ) : ℝ) := by push_cast; ring
    rw [heq, e2] at e1
    push_cast at e1 ⊢
    linarith
  have hrat : mrGamma s t ^ s * p = ((2 * k + 1) / 2) ^ s * mrQss s := by exact_mod_cast hreal
  have hk : ((2 * k + 1) / 2 : ℚ) ≠ 0 := by
    intro h0
    have : (2 * k + 1 : ℚ) = 0 := by linarith [h0]
    have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  have hpq : (p : ℚ) = ((2 * k + 1) / 2) ^ s * (mrQss s / mrGamma s t ^ s) := by
    field_simp; linarith [hrat]
  have hval := congrArg (padicValRat p) hpq
  rw [padicValRat.self hp.out.one_lt, padicValRat.mul (pow_ne_zero _ hk)
    (div_ne_zero hQ.ne' (pow_ne_zero _ hγ.ne')), hv, padicValRat.pow] at hval
  have : (s : ℤ) * padicValRat p ((2 * k + 1) / 2) = 1 := by linarith
  have h2 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  rcases lt_trichotomy (padicValRat p ((2 * k + 1) / 2)) 0 with h | h | h <;> nlinarith

/-- **Exact rational form of the rounding**: if `k ≥ 1` and `(2k-1)^s Q_s^s ≤ 2^s γ_t^s p < (2k+1)^s Q_s^s`,
then the mixed-radix rule takes `h_t = k`. -/
theorem mrRuleH_eq_of_bracket (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ s - 1)
    (k : ℕ) (hk : 1 ≤ k)
    (h1 : ((2 * k - 1 : ℚ)) ^ s * mrQss s ≤ 2 ^ s * mrGamma s t ^ s * p)
    (h2 : 2 ^ s * mrGamma s t ^ s * p < ((2 * k + 1 : ℚ)) ^ s * mrQss s) :
    mrRuleH s p t = k := by
  set x : ℝ := (mrGamma s t : ℝ) * mrU s p with hx
  have hγ : (0 : ℝ) < mrGamma s t := by exact_mod_cast mrGamma_pos s t hs ht1 ht
  have hx0 : 0 ≤ x := by have := mrU_pos s p hs hp; positivity
  have hQ := mrQss_pos_real s hs
  have hxs : (2 * x) ^ s * mrQss s = 2 ^ s * (mrGamma s t : ℝ) ^ s * p := by
    rw [hx, mul_pow, mul_pow, mul_assoc, mul_assoc, mul_comm (mrU s p ^ s), ← mrPu, mrPu_mrU s p hs]
    ring
  have h1' : ((2 * k - 1 : ℝ)) ^ s * mrQss s ≤ (2 * x) ^ s * mrQss s := by
    rw [hxs]; exact_mod_cast h1
  have h2' : (2 * x) ^ s * mrQss s < ((2 * k + 1 : ℝ)) ^ s * mrQss s := by
    rw [hxs]; exact_mod_cast h2
  have hk1 : (0 : ℝ) ≤ 2 * k - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have a1 : (2 * k - 1 : ℝ) ≤ 2 * x :=
    (pow_le_pow_iff_left₀ hk1 (by positivity) (by omega)).mp (le_of_mul_le_mul_right h1' hQ)
  have a2 : 2 * x < 2 * k + 1 :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp (lt_of_mul_lt_mul_right h2' hQ.le)
  have hr : round x = k := by
    rw [round_eq, Int.floor_eq_iff]; push_cast; constructor <;> linarith
  unfold mrRuleH
  rw [← hx, hr]
  simp only [Int.toNat_natCast]
  omega

/-! ## `thm:MRall` -/

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
  set a : ℝ := (mrUmin s : ℝ) with ha
  have ha0 : 0 < a := by rw [ha]; exact_mod_cast mrUmin_pos s (by omega)
  set u0 : ℝ := 2 * a with hu0
  set ub : ℝ := max u0 (2 * u0 * mrF s u0) with hub
  have hM := mrF_mono s (by omega)
  have hu0a : a < u0 := by rw [hu0]; linarith
  have hub0 : u0 ≤ ub := le_max_left _ _
  have huba : a < ub := lt_of_lt_of_le hu0a hub0
  have hFb : mrF s ub ≤ 1 / 2 := by
    have h1 : ub * mrF s ub ≤ u0 * mrF s u0 := hM.2 hu0a huba hub0
    have h2 : 2 * u0 * mrF s u0 ≤ ub := le_max_right _ _
    have hub_pos : 0 < ub := by linarith
    nlinarith
  have hS : {u : ℝ | a < u ∧ mrF s u < 1}.Nonempty := ⟨ub, huba, by linarith⟩
  have hbdd : BddBelow {u : ℝ | a < u ∧ mrF s u < 1} := ⟨a, fun u hu => hu.1.le⟩
  have hu1a : a ≤ mrU1 s := le_csInf hS fun u hu => hu.1.le
  have hu1b : mrU1 s ≤ ub := csInf_le hbdd ⟨huba, by linarith⟩
  refine ⟨huba, hFb, hS, hu1a, hu1b, ?_⟩
  unfold mrP1
  have hQ := mrQss_pos_real s (by omega)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hu1b s) hQ.le

/-- The core of `thm:MRall`(b), (c): if `u(p) ≥ v > u_min` with `F(v) < 1`, the rule has `Γ/p ≤ F(u(p)) < 1`
and `Γ/p ≤ v F(v)/u(p)`. -/
lemma mrall_core (s p : ℕ) (hs : 3 ≤ s) (hp : 1 ≤ p) (v : ℝ) (hv : (mrUmin s : ℝ) < v) (hF : mrF s v < 1)
    (hvu : v ≤ mrU s p) :
    mrCost s p (mrRuleH s p) < p ∧ (mrCost s p (mrRuleH s p) : ℝ) / p ≤ mrF s (mrU s p) ∧
      mrF s (mrU s p) < 1 ∧ (mrCost s p (mrRuleH s p) : ℝ) / p ≤ v * mrF s v / mrU s p := by
  have hM := mrF_mono s (by omega)
  have hu : (mrUmin s : ℝ) < mrU s p := lt_of_lt_of_le hv hvu
  have hFu : mrF s (mrU s p) ≤ mrF s v := hM.1.2 hv hu hvu
  have hF1 : mrF s (mrU s p) < 1 := lt_of_le_of_lt hFu hF
  have hb := MRbound s p hs hp (mrRuleH s p) hu
    (fun t h1 h2 => mrRuleH_bound s p (by omega) hu t h1 h2)
    ((mrFrow0_le_mrF s (by omega) _).trans hF1.le)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlt : (mrCost s p (mrRuleH s p) : ℝ) < p := by
    have := lt_of_le_of_lt hb hF1; rwa [div_lt_one hp0] at this
  have huF : mrU s p * mrF s (mrU s p) ≤ v * mrF s v := hM.2 hv hu hvu
  have hupos := mrU_pos s p (by omega) hp
  refine ⟨by exact_mod_cast hlt, hb, hF1, hb.trans ?_⟩
  rw [le_div_iff₀ hupos, mul_comm]; exact huF

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
  have hp : 1 ≤ p := by omega
  obtain ⟨-, -, hS, hu1a, -, -⟩ := MRall_a s hs
  have ha0 : (0 : ℝ) ≤ mrUmin s := by exact_mod_cast (mrUmin_pos s (by omega)).le
  -- `u(p) > u_1`
  have hu1 : mrU1 s < mrU s p := by
    rw [lt_mrU_iff s p (by omega) hp (ha0.trans hu1a)]; exact hp1
  obtain ⟨v, ⟨hva, hvF⟩, hvu⟩ := exists_lt_of_csInf_lt hS hu1
  have hΓ := (mrall_core s p hs hp v hva hvF hvu.le).1
  refine ⟨hΓ, fun zθ hroot hplace => ?_⟩
  exact MR s p hs hsp.le (mrRuleH s p) (fun t h1 h2 => le_max_left _ _) hΓ zθ hroot hplace

/-- **`thm:MRall`(c)**: for every real (in particular every rational) `u^* > u_min` with `F(u^*) < 1` and every
prime `p ≥ max(Q_s^s u^{*s}, s)`, the mixed-radix rule has `Γ < p` and
`1 - (p - Γ)/p = Γ/p ≤ C'_s p^{-1/s}` with `C'_s = Q_s u^* F(u^*)`. -/
theorem MRall_c (s p : ℕ) [hpr : Fact p.Prime] (hs : 3 ≤ s) (us : ℝ) (hus : (mrUmin s : ℝ) < us)
    (hF : mrF s us < 1) (hp : (mrQss s : ℝ) * us ^ s ≤ p) (hsp : s ≤ p) :
    mrCost s p (mrRuleH s p) < p ∧
      1 - ((p : ℝ) - mrCost s p (mrRuleH s p)) / p = (mrCost s p (mrRuleH s p) : ℝ) / p ∧
      (mrCost s p (mrRuleH s p) : ℝ) / p ≤ mrCp s us * (p : ℝ) ^ (-(1 : ℝ) / s) := by
  have hp1 : 1 ≤ p := hpr.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have ha0 : (0 : ℝ) ≤ mrUmin s := by exact_mod_cast (mrUmin_pos s (by omega)).le
  have hvu : us ≤ mrU s p := (le_mrU_iff s p (by omega) hp1 (ha0.trans hus.le)).mpr hp
  obtain ⟨hΓ, -, -, hb⟩ := mrall_core s p hs hp1 us hus hF hvu
  refine ⟨hΓ, by field_simp; ring, hb.trans (le_of_eq ?_)⟩
  unfold mrCp mrU
  rw [neg_div, Real.rpow_neg (Nat.cast_nonneg _)]
  have := mrQ_pos s (by omega)
  have : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / s) := Real.rpow_pos_of_pos hp0 _
  field_simp

/-- `F` at a rational point is the rational `F` (exact evaluation of `tab:P1`, `tab:LFY`). -/
theorem mrF_cast (s : ℕ) (hs : 1 ≤ s) (q : ℚ) : ((mrF s q : ℚ) : ℝ) = mrF s (q : ℝ) := by
  have hne : (range s).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  unfold mrF
  rw [dite_eq_left_of_eq_true (eq_true hne), dite_eq_left_of_eq_true (eq_true hne),
    Finset.apply_sup'_eq_sup'_comp hne _ (fun x y => Rat.cast_max x y)]
  refine Finset.sup'_congr hne rfl fun c _ => ?_
  simp only [Function.comp_apply, mrFrow, mrEta, mrNuP, mrNuM, mrPu]
  split_ifs <;> push_cast <;> rfl

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
  have hFr : mrF s (us : ℝ) < 1 := by rw [← mrF_cast s (by omega)]; exact_mod_cast hF
  have husr : (mrUmin s : ℝ) < us := by exact_mod_cast hus
  have ha0 : (0 : ℝ) ≤ mrUmin s := by exact_mod_cast (mrUmin_pos s (by omega)).le
  have hus0 : (0 : ℝ) ≤ us := ha0.trans husr.le
  have hPr : (mrQss s : ℝ) * (us : ℝ) ^ s ≤ P := by exact_mod_cast hP
  have hFnn : 0 ≤ mrF s (us : ℝ) := (mrF_mono s (by omega)).1.1 _ husr
  have hCp : mrCp s us ≤ C := by
    have hx : 0 ≤ (us : ℝ) * mrF s (us : ℝ) := mul_nonneg hus0 hFnn
    have hCr : (mrQss s : ℝ) * ((us : ℝ) * mrF s (us : ℝ)) ^ s ≤ (C : ℝ) ^ s := by
      rw [← mrF_cast s (by omega)]; exact_mod_cast hC
    unfold mrCp
    rw [mul_assoc]
    refine (pow_le_pow_iff_left₀ (mul_nonneg (mrQ_pos s (by omega)).le hx) (by exact_mod_cast hC0)
      (by omega : s ≠ 0)).mp ?_
    rw [mul_pow, mrQ_pow s (by omega)]; exact hCr
  refine ⟨?_, hCp, fun p hp hPp hsp => ?_⟩
  · have hS := (MRall_a s hs).2.2.1
    have hbdd : BddBelow {u : ℝ | (mrUmin s : ℝ) < u ∧ mrF s u < 1} := ⟨mrUmin s, fun u hu => hu.1.le⟩
    have hu1 : mrU1 s ≤ us := csInf_le hbdd ⟨husr, hFr⟩
    have hu1a := (MRall_a s hs).2.2.2.1
    unfold mrP1
    refine le_trans ?_ hPr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha0.trans hu1a) hu1 s)
      (mrQss_pos_real s (by omega)).le
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hΓ, he, hb⟩ := MRall_c s p hs us husr hFr (hPr.trans hPp) hsp
    refine ⟨hΓ, ?_⟩
    rw [he]
    refine hb.trans (mul_le_mul_of_nonneg_right hCp (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end GeoSeq
