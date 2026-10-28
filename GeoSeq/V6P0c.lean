/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V6Defs
public import GeoSeq.V5P0
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# GeoSeq stage V6: `prop:P0`(c) (the limit hierarchy gives `𝒫(p)` for all large `p`)

* `tendsto_NP`: `N_t^+(p) → N̄_t` as `p → ∞` (when `λ_1 ≤ 1`, which the hypotheses of (c) give);
  `tendsto_MP`: `M^+(p)` converges.
* **`P0_c`** (`prop:P0`(c)): if the design satisfies the limit hierarchy, `0 < ε_{⋆←C} < ½`, `x² + y² > 1` and
  `1 - 2(s-2)ε_{C←C} - 2ε_{C←⋆} > 1/√2` (and the positivity of the fractions and of `u` required by `def:BS`),
  then `𝒫(p)` holds for all large real `p`.
* **`P0_c_nat`** (the last sentence of `prop:P0`): under the same hypotheses, above every bound there is a natural
  number `p₀` with `𝒫(p₀)` (over `ℚ`, a decidable predicate — so the least such `p₀` is effectively computable by
  search, and `P0_seq` / `P0_design` apply with `C'' = M⋆^+(p₀)`).
-/

namespace GeoSeq

open Finset Filter Topology

section Lim

variable {s : ℕ}

lemma tendsto_p_div (a u : ℝ) (hu : 0 < u) :
    Tendsto (fun p : ℝ => p / (a * (u * p - 2))) atTop (𝓝 (1 / (a * u))) := by
  by_cases ha : a = 0
  · subst ha; simp
  have h2 : Tendsto (fun p : ℝ => 2 / p) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun p : ℝ => a * (u - 2 / p)) atTop (𝓝 (a * u)) := by
    simpa using (tendsto_const_nhds.sub h2).const_mul a
  have h3 := h1.inv₀ (mul_ne_zero ha hu.ne')
  rw [one_div]
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with p hp
  have e : a * (u - 2 / p) = a * (u * p - 2) / p := by field_simp
  rw [e, inv_div]

/-- `N_t^+(p) → N̄_t` (`app:LFdata`, proof of `prop:P0`(c)), provided `λ_1 ≤ 1` in the column. -/
lemma tendsto_NP (D : StagData s) (hu : 0 < (D.u : ℝ)) (c' : Fin s) (h0 : stLam (K := ℝ) D c' 0 ≤ 1) (t : ℕ) :
    Tendsto (fun p : ℝ => stNP D p c' t) atTop (𝓝 (stNbar D c' t)) := by
  induction t with
  | zero =>
    set a : ℝ := (stCoef D c' (D.rows c' 0) : ℝ) with ha
    set f : ℝ := (stFrac D c' (D.rows c' 0) : ℝ) with hf
    have hlim : Tendsto (fun p : ℝ => ((1 - 2 * f) + p⁻¹) * (p / (a * ((D.u : ℝ) * p - 2)))) atTop
        (𝓝 (((1 - 2 * f) + 0) * (1 / (a * D.u)))) :=
      (tendsto_const_nhds.add tendsto_inv_atTop_zero).mul (tendsto_p_div a _ hu)
    have hmax := (tendsto_const_nhds (x := (2 : ℝ))).add ((tendsto_const_nhds (x := (0 : ℝ))).max hlim)
    have hval : 2 + max 0 (((1 - 2 * f) + 0) * (1 / (a * D.u))) = stNbar D c' 0 := by
      have hf1 : 0 ≤ 1 - 2 * f := by simp only [stLam] at h0; rw [hf]; linarith
      have ha0 : 0 ≤ a := by positivity
      rw [max_eq_right (by positivity)]
      simp only [stNbar, stLam, stMu]
      rw [← ha, ← hf]; ring
    rw [← hval]
    refine hmax.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    simp only [stNP, stEll, stNuM]
    rw [← ha, ← hf]
    congr 2
    rw [← mul_div_assoc]
    congr 1
    field_simp
    ring
  | succ t ih =>
    exact ih.add (tendsto_p_div (stCoef D c' (D.rows c' (t + 1)) : ℝ) _ hu)

lemma tendsto_foldr (cs : Fin s) (g : ℝ → Fin s → ℝ) (gl : Fin s → ℝ)
    (hg : ∀ c, c ≠ cs → Tendsto (fun p => g p c) atTop (𝓝 (gl c))) (l : List (Fin s)) :
    Tendsto (fun p => l.foldr (fun c m => if c = cs then m else max (g p c) m) 0) atTop
      (𝓝 (l.foldr (fun c m => if c = cs then m else max (gl c) m) 0)) := by
  induction l with
  | nil => simpa using tendsto_const_nhds
  | cons c l ih =>
    by_cases hc : c = cs
    · simpa [List.foldr, hc] using ih
    · simp only [List.foldr_cons, if_neg hc]
      exact (hg c hc).max ih

/-- `lim M^+(p)`: the fold of `2N̄_{s-1} - 1` over the columns `i ∈ C`. -/
noncomputable def stMbar (D : StagData s) : ℝ :=
  (List.finRange s).foldr (fun c m => if c = D.cs then m else max (2 * stNbar D c (s - 2) - 1) m) 0

lemma tendsto_MP (D : StagData s) (hu : 0 < (D.u : ℝ)) (h0 : ∀ c', stLam (K := ℝ) D c' 0 ≤ 1) :
    Tendsto (fun p : ℝ => stMP D p) atTop (𝓝 (stMbar D)) :=
  tendsto_foldr D.cs (fun p c => 2 * stNP D p c (s - 2) - 1) (fun c => 2 * stNbar D c (s - 2) - 1)
    (fun c _ => ((tendsto_NP D hu c (h0 c) (s - 2)).const_mul 2).sub tendsto_const_nhds) _

/-- `f(p) + b ≤ a p` eventually, for convergent `f` and `a > 0`. -/
lemma ev_lin (f : ℝ → ℝ) (l a b : ℝ) (hf : Tendsto f atTop (𝓝 l)) (ha : 0 < a) :
    ∀ᶠ p in atTop, f p + b ≤ a * p := by
  filter_upwards [hf.eventually (gt_mem_nhds (lt_add_one l)), eventually_ge_atTop ((l + 1 + |b|) / a)]
    with p h1 h2
  have := (div_le_iff₀ ha).mp h2
  linarith [le_abs_self b]

/-- `g(p) p + b ≤ c p` eventually, for `g → l < c`. -/
lemma ev_scaled (g : ℝ → ℝ) (l c b : ℝ) (hg : Tendsto g atTop (𝓝 l)) (hlc : l < c) :
    ∀ᶠ p in atTop, g p * p + b ≤ c * p := by
  have hm : l < (l + c) / 2 := by linarith
  have hd : 0 < (c - l) / 2 := by linarith
  filter_upwards [hg.eventually (gt_mem_nhds hm), eventually_ge_atTop 0,
    eventually_ge_atTop (|b| / ((c - l) / 2))] with p h1 h2 h3
  have h4 := (div_le_iff₀ hd).mp h3
  have h5 : g p * p ≤ (l + c) / 2 * p := mul_le_mul_of_nonneg_right h1.le h2
  nlinarith [le_abs_self b]

end Lim

section Main

variable {s : ℕ}

/-- Under the hypotheses of `prop:P0`(c), every window fraction that occurs as a first row is at most `½`. -/
lemma lam0_le_one (D : StagData s) (hv : D.Valid) (hs : 2 ≤ s) (hCS : 0 < D.eCS) (hCC : 0 < D.eCC)
    (hSC2 : D.eSC < 1 / 2) (hzb : 0 < 1 - 2 * ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS) (c' : Fin s) :
    stLam (K := ℝ) D c' 0 ≤ 1 := by
  have hcc0 : (0 : ℝ) < D.eCC := by exact_mod_cast hCC
  have hcs0 : (0 : ℝ) < D.eCS := by exact_mod_cast hCS
  have hsc : (D.eSC : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hSC2
    rwa [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by push_cast; ring] at h
  have hr : D.rows c' 0 ≠ c' := hv.1 c' 0 (by omega)
  have hs2 : (0 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [stLam, stFrac]
  split_ifs with h1 h2
  · push_cast; nlinarith
  · push_cast; linarith
  · have h3 : 3 ≤ s := three_le_of (Ne.symm hr) h1 h2
    have : (1 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ s - 2 by omega)
    push_cast; nlinarith

/-- **`prop:P0`(c)**: if the design satisfies the limit hierarchy (`LimHier`), `0 < ε_{⋆←C} < ½`,
`x² + y² > 1` and `1 - 2(s-2)ε_{C←C} - 2ε_{C←⋆} > 1/√2` (with the positive fractions and `u > 0` of `def:BS`), then
`𝒫(p)` holds for all large real `p`. -/
theorem P0_c (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hu : 0 < D.u) (hCS : 0 < D.eCS) (hCC : 0 < D.eCC)
    (hSC : 0 < D.eSC) (hSC2 : D.eSC < 1 / 2) (hxy : 1 < stX D ^ 2 + stY D ^ 2)
    (hz : 1 / Real.sqrt 2 < 1 - 2 * ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS) (hH : LimHier (K := ℝ) D) :
    ∀ᶠ p in atTop, StP D (p : ℝ) := by
  obtain ⟨hH1, hH2, hH3⟩ := hH
  have huR : (0 : ℝ) < D.u := by exact_mod_cast hu
  set zb : ℝ := 1 - 2 * ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS with hzbdef
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hzs : 1 < zb * Real.sqrt 2 := by rwa [div_lt_iff₀ hs0] at hz
  have hzb0 : 0 < zb := by nlinarith
  have hzb2 : 1 < 2 * zb ^ 2 := by nlinarith
  have h0 := lam0_le_one D hv hs hCS hCC hSC2 hzb0
  have hNP := fun c' t => tendsto_NP D huR c' (h0 c') t
  have hMP := tendsto_MP D huR h0
  have hMst : Tendsto (fun p : ℝ => stMstP D p) atTop (𝓝 (stNbar D D.cs (s - 2))) := hNP D.cs (s - 2)
  have hMPp : Tendsto (fun p : ℝ => stMP D p / p) atTop (𝓝 0) := hMP.div_atTop tendsto_id
  have hxyR : (1 : ℝ) < (stX D : ℝ) ^ 2 + (stY D : ℝ) ^ 2 := by exact_mod_cast hxy
  have hx : zb ≤ (stX D : ℝ) := by
    have : (0 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) * D.eCC := by
      have : (0 : ℝ) < D.eCC := by exact_mod_cast hCC
      positivity
    simp only [stX, hzbdef]; push_cast; linarith
  have hscR : (0 : ℝ) < 1 - 2 * D.eSC := by
    have : (D.eSC : ℝ) < 1 / 2 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hSC2
      rwa [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by push_cast; ring] at h
    linarith
  -- (P1)
  have e1 : ∀ᶠ p : ℝ in atTop, 2 < (D.u : ℝ) * p := by
    filter_upwards [eventually_gt_atTop (2 / (D.u : ℝ))] with p hp
    rwa [div_lt_iff₀ huR, mul_comm] at hp
  -- (P2)
  have e2 : ∀ᶠ p : ℝ in atTop, ∀ c' : Fin s, stNuP D p c' 0 ≤ stEll D p c' 0 ∧
      ∀ t < s - 2, stNP D p c' t * stNuP D p c' (t + 1) ≤ stEll D p c' (t + 1) := by
    refine eventually_all.2 fun c' => ?_
    have ea := ev_scaled (fun _ => stMu (K := ℝ) D c' 0) _ _ 1 tendsto_const_nhds (hH1 c').1
    have eb : ∀ᶠ p : ℝ in atTop, ∀ t : Fin (s - 2),
        stNP D p c' t * stNuP D p c' ((t : ℕ) + 1) ≤ stEll D p c' ((t : ℕ) + 1) := by
      refine eventually_all.2 fun t => ?_
      have := ev_scaled (fun p => stNP D p c' t * stMu (K := ℝ) D c' ((t : ℕ) + 1)) _ _ 1
        ((hNP c' t).mul tendsto_const_nhds) ((hH1 c').2 t t.2)
      filter_upwards [this] with p hp
      simp only [stNuP, stEll, stMu, stLam] at hp ⊢
      linarith
    filter_upwards [ea, eb] with p hpa hpb
    refine ⟨?_, fun t ht => hpb ⟨t, ht⟩⟩
    simp only [stNuP, stEll, stMu, stLam] at hpa ⊢
    linarith
  -- (P3)
  have e3 : ∀ᶠ p : ℝ in atTop, ∀ c c' : Fin s, c ≠ D.cs → c ≠ c' →
      ((D.nI c c').natAbs : ℝ) * ((D.u : ℝ) * p) ≤ (stFrac D c' c : ℝ) * p - 1 := by
    refine eventually_all.2 fun c => eventually_all.2 fun c' => ?_
    by_cases h : c ≠ D.cs ∧ c ≠ c'
    · have := ev_scaled (fun _ => (D.u : ℝ) * ((D.nI c c').natAbs : ℝ)) _ _ 1 tendsto_const_nhds
        (hH2 c c' h.1 h.2)
      filter_upwards [this] with p hp _ _
      linarith
    · exact Eventually.of_forall fun p h1 h2 => absurd ⟨h1, h2⟩ h
  have e3h : ∀ᶠ p : ℝ in atTop, ∀ i : Fin s, i ≠ D.cs →
      ((D.nI D.cs i).natAbs : ℝ) * ((D.u : ℝ) * p) ≤ 2 * ((D.eSC : ℝ) * p - 1) - 1 := by
    refine eventually_all.2 fun i => ?_
    by_cases h : i ≠ D.cs
    · have := ev_scaled (fun _ => (D.u : ℝ) * ((D.nI D.cs i).natAbs : ℝ)) _ _ 3 tendsto_const_nhds (hH3 i h)
      filter_upwards [this] with p hp _
      linarith
    · exact Eventually.of_forall fun p h1 => absurd h1 h
  -- (P4)
  have e4 : ∀ᶠ p : ℝ in atTop, 2 * (stX D : ℝ) * stMP D p + 2 * (stY D : ℝ) * (stMstP D p + 1 / 2) ≤
      p * ((stX D : ℝ) ^ 2 + (stY D : ℝ) ^ 2 - 1) := by
    have := ev_lin (fun p : ℝ => 2 * (stX D : ℝ) * stMP D p + 2 * (stY D : ℝ) * (stMstP D p + 1 / 2)) _
      ((stX D : ℝ) ^ 2 + (stY D : ℝ) ^ 2 - 1) 0
      ((hMP.const_mul _).add ((hMst.add tendsto_const_nhds).const_mul _)) (by linarith)
    filter_upwards [this] with p hp
    linarith
  -- (P5)
  have hZ : Tendsto (fun p : ℝ => stZ D p) atTop (𝓝 (zb - 0)) := by
    have := (tendsto_const_nhds (x := zb)).sub hMPp
    refine this.congr' (Eventually.of_forall fun p => ?_)
    simp only [stZ, hzbdef]
  rw [sub_zero] at hZ
  have e5a : ∀ᶠ p : ℝ in atTop, 0 ≤ stZ D p := (hZ.eventually (lt_mem_nhds hzb0)).mono fun _ h => h.le
  have e5b : ∀ᶠ p : ℝ in atTop, 1 ≤ 2 * stZ D p ^ 2 :=
    (((hZ.pow 2).const_mul 2).eventually (lt_mem_nhds hzb2)).mono fun _ h => h.le
  -- (P6)
  have e6a : ∀ᶠ p : ℝ in atTop,
      (2 * ((s - 2 : ℕ) : ℝ) * (D.eCC : ℝ) + 2 * (D.eCS : ℝ)) * p + stMP D p + 2 ≤ p - 1 := by
    filter_upwards [ev_lin _ _ zb 3 hMP hzb0] with p hp
    simp only [hzbdef] at hp
    linarith
  have e6b : ∀ᶠ p : ℝ in atTop, 2 * (D.eSC : ℝ) * p + 2 * stMstP D p + 2 < p - 1 := by
    filter_upwards [ev_lin _ _ _ 4 (hMst.const_mul 2) hscR] with p hp
    linarith
  have e6c : ∀ᶠ p : ℝ in atTop, stMP D p / p < (stX D : ℝ) := hMPp.eventually (gt_mem_nhds (by linarith))
  filter_upwards [e1, e2, e3, e3h, e4, e5a, e5b, e6a, e6b, e6c] with p h1 h2 h3 h3h h4 h5a h5b h6a h6b h6c
  exact ⟨h1, h2, h3, h3h, ⟨hxyR, h4⟩, ⟨h5a, h5b⟩, h6a, h6b, h6c⟩

/-- **`prop:P0`, last sentence** ("under the hypotheses of (c) such a `p₀` exists"): above every bound `N` there is
a natural number `p₀` with `𝒫(p₀)`, as an exact rational statement (decidable). -/
theorem P0_c_nat (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hu : 0 < D.u) (hCS : 0 < D.eCS)
    (hCC : 0 < D.eCC) (hSC : 0 < D.eSC) (hSC2 : D.eSC < 1 / 2) (hxy : 1 < stX D ^ 2 + stY D ^ 2)
    (hz : 1 / Real.sqrt 2 < 1 - 2 * ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS) (hH : LimHier (K := ℝ) D) (N : ℕ) :
    ∃ p0 : ℕ, N ≤ p0 ∧ 0 < p0 ∧ StP D (p0 : ℚ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (P0_c D hs hv hu hCS hCC hSC hSC2 hxy hz hH)
  refine ⟨max (N + 1) ⌈M⌉₊, le_trans (Nat.le_succ N) (le_max_left _ _),
    lt_of_lt_of_le (Nat.succ_pos N) (le_max_left _ _), ?_⟩
  rw [StP_cast]
  have : M ≤ ((max (N + 1) ⌈M⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil M).trans (by exact_mod_cast le_max_right _ _)
  simpa using hM _ this

end Main

end GeoSeq
