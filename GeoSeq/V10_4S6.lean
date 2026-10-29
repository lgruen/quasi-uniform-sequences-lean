/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4Main
public import GeoSeq.V10_4S6Defs
public import GeoSeq.V10_4S6ca0
public import GeoSeq.V10_4S6ca1
public import GeoSeq.V10_4S6ca2
public import GeoSeq.V10_4S6ca3
public import GeoSeq.V10_4S6ca4
public import GeoSeq.V10_4S6ca5
public import GeoSeq.V10_4S6ca6
public import GeoSeq.V10_4S6ca7
public import GeoSeq.V10_4S6ca8
public import GeoSeq.V10_4S6ca9
public import GeoSeq.V10_4S6ca10

@[expose] public section

/-!
# GeoSeq stage V10-4 (part 4): the improved `s = 6` block design, `sep(P_{36K}) ≥ 1 - 15/p`

The design `blk6dF` keeps the off-diagonal entries of `U*_6` and sets `F_0[c][c] = -(3, 12, 13, 14, 13, 13)` (the free
diagonal; `U*_6` itself gives `1 - 44/p` for `p ≥ 5 a*_6 + 4 = 219`).

* `blk6d_netsForm`, `blk6G_deg`, **`blk6d_reach`**: reachability (`def:block`) at the places `0, 1, …, 1/5` with
  `v = (1, 1, 2, 3, 4, 5)`, via the nets' form `F_n[i][c] = w̃_{ic} G_{c,n}(ỹ_{ic})` and the transfer
  `reach_of_netsForm` (every prime `p ≥ 7`).
* `blk6d_chk` (121 kernel evaluations, `GeoSeq/V10_4S6ca*.lean`), **`blk6d_signclass`**: the sign-class condition with
  `A = 14` (one evaluation of the checker at `P = 6367`, `6 · 46² + 2 · 14 + 3 < 2P`).
* **`blk6d_LB_proof`**: `LB(F) ≥ 1 - 15/p` for every prime `p ≥ 125` (`sc_LB`); `axis_term_depth`,
  **`blk6d_LB_eq`**: the axis step along the place `1/3` with carry length `4` attains it (`LB(F) = 1 - 15/p`).
* **`blk6d_block`**: for every prime `p ≥ 125` and `θ ≠ 0`, a digital `(0,6)`-sequence, the design relation at every
  `P_{36K}`, and `sep(P_{36K}) ≥ 1 - 15/p`.
-/

namespace GeoSeq

open Finset Polynomial

/-! ## The checker: one evaluation at `P = 6367` -/

lemma blk6d_hM : ∀ j, j + 2 ≤ 6 → ∀ i c, blk6dM j i c = ∑ n ∈ range (j + 1), blk6dF n i c := by
  intro j hj; have : j ≤ 4 := by omega
  interval_cases j <;> decide +kernel

lemma blk6d_hB : ∀ j, j + 2 ≤ 6 → ∀ i c, |blk6dM j i c| ≤ blk6dB i c := by
  intro j hj; have : j ≤ 4 := by omega
  interval_cases j <;> decide +kernel

lemma blk6d_rows : (∀ i, ∑ c, blk6dB i c ≤ ((46 : ℕ) : ℤ)) ∧ ∀ i, ∑ c, blk6dB i c ≤ 63 := by decide +kernel

lemma blk6d_opts : blk6dO0 :: blk6dO1 :: blk6dRest2 = List.ofFn fun k => caOpts blk6dM (Fin.rev k) := by
  decide +kernel

lemma blk6d_st0 : blk6dSt0 = caStart 6 := by decide +kernel

lemma prime6367 : Nat.Prime 6367 := by norm_num

/-- The checker splits over the options of the first two coordinates (the 121 parts are evaluated in
`GeoSeq/V10_4S6ca*.lean`). -/
theorem blk6d_chk_of (h : ∀ x ∈ blk6dO0, ∀ y ∈ blk6dO1,
    allFold (· + ·) (caLeaf 6 6367 14) blk6dRest2 ((0, blk6dSt0) + x + y) = true) :
    caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true := by
  unfold caCheck
  simp only [allFold]
  rw [List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro y hy
  exact h x hx y hy

/-- The checker for `blk6dF` (`A = 14`) at `P = 6367`, assembled from the 121 kernel evaluations (`lake build` only:
the evaluations are compared one module per configuration, `comparatorGeoSeqV10_4ca<k>.json`). -/
theorem blk6d_chk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true := by
  refine blk6d_chk_of fun x hx y hy => ?_
  simp only [blk6dO0, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [blk6dO1, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [blk6d_chk0_0, blk6d_chk0_1, blk6d_chk0_2, blk6d_chk0_3, blk6d_chk0_4, blk6d_chk0_5, blk6d_chk0_6, blk6d_chk0_7, blk6d_chk0_8, blk6d_chk0_9, blk6d_chk0_10, blk6d_chk1_0, blk6d_chk1_1, blk6d_chk1_2, blk6d_chk1_3, blk6d_chk1_4, blk6d_chk1_5, blk6d_chk1_6, blk6d_chk1_7, blk6d_chk1_8, blk6d_chk1_9, blk6d_chk1_10, blk6d_chk2_0, blk6d_chk2_1, blk6d_chk2_2, blk6d_chk2_3, blk6d_chk2_4, blk6d_chk2_5, blk6d_chk2_6, blk6d_chk2_7, blk6d_chk2_8, blk6d_chk2_9, blk6d_chk2_10, blk6d_chk3_0, blk6d_chk3_1, blk6d_chk3_2, blk6d_chk3_3, blk6d_chk3_4, blk6d_chk3_5, blk6d_chk3_6, blk6d_chk3_7, blk6d_chk3_8, blk6d_chk3_9, blk6d_chk3_10, blk6d_chk4_0, blk6d_chk4_1, blk6d_chk4_2, blk6d_chk4_3, blk6d_chk4_4, blk6d_chk4_5, blk6d_chk4_6, blk6d_chk4_7, blk6d_chk4_8, blk6d_chk4_9, blk6d_chk4_10, blk6d_chk5_0, blk6d_chk5_1, blk6d_chk5_2, blk6d_chk5_3, blk6d_chk5_4, blk6d_chk5_5, blk6d_chk5_6, blk6d_chk5_7, blk6d_chk5_8, blk6d_chk5_9, blk6d_chk5_10, blk6d_chk6_0, blk6d_chk6_1, blk6d_chk6_2, blk6d_chk6_3, blk6d_chk6_4, blk6d_chk6_5, blk6d_chk6_6, blk6d_chk6_7, blk6d_chk6_8, blk6d_chk6_9, blk6d_chk6_10, blk6d_chk7_0, blk6d_chk7_1, blk6d_chk7_2, blk6d_chk7_3, blk6d_chk7_4, blk6d_chk7_5, blk6d_chk7_6, blk6d_chk7_7, blk6d_chk7_8, blk6d_chk7_9, blk6d_chk7_10, blk6d_chk8_0, blk6d_chk8_1, blk6d_chk8_2, blk6d_chk8_3, blk6d_chk8_4, blk6d_chk8_5, blk6d_chk8_6, blk6d_chk8_7, blk6d_chk8_8, blk6d_chk8_9, blk6d_chk8_10, blk6d_chk9_0, blk6d_chk9_1, blk6d_chk9_2, blk6d_chk9_3, blk6d_chk9_4, blk6d_chk9_5, blk6d_chk9_6, blk6d_chk9_7, blk6d_chk9_8, blk6d_chk9_9, blk6d_chk9_10, blk6d_chk10_0, blk6d_chk10_1, blk6d_chk10_2, blk6d_chk10_3, blk6d_chk10_4, blk6d_chk10_5, blk6d_chk10_6, blk6d_chk10_7, blk6d_chk10_8, blk6d_chk10_9, blk6d_chk10_10]

/-- The sign-class condition for `blk6dF` with `A = 14`, from the evaluation of the checker at `P = 6367`. -/
theorem blk6d_signclass_of (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true) :
    SignClass blk6dM 14 := by
  haveI : Fact (Nat.Prime 6367) := ⟨prime6367⟩
  refine ca_signclass (by norm_num) blk6dF blk6dM blk6d_hM blk6dB blk6d_hB 46 14 blk6d_rows.1 6367 (by norm_num)
    (by norm_num) fun K => ?_
  exact caCheck_sound (p := 6367) (by norm_num) blk6dF blk6dM blk6d_hM blk6dB blk6d_hB blk6d_rows.2 _ blk6d_opts _
    blk6d_st0 14 (by norm_num) hchk K

/-- The sign-class condition for `blk6dF` with `A = 14` (unconditional; `lake build` only). -/
theorem blk6d_signclass : SignClass blk6dM 14 := blk6d_signclass_of blk6d_chk

variable {p : ℕ} [Fact p.Prime]

/-! ## Reachability -/

lemma sumX_natDegree {F : Type*} [Field F] (cf : ℕ → F) (n : ℕ) (hn : cf n ≠ 0) :
    (∑ k ∈ range (n + 1), C (cf k) * X ^ k).natDegree = n ∧ (∑ k ∈ range (n + 1), C (cf k) * X ^ k).coeff n = cf n := by
  have hc : (∑ k ∈ range (n + 1), C (cf k) * X ^ k).coeff n = cf n := by
    simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    rw [sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero]) (by simp), if_pos rfl, mul_one]
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hc]; exact hn), hc⟩
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rw [mem_range] at hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The nets-form polynomials of `blk6dF` have exact degree `n` (every prime `p ≥ 5`). -/
theorem blk6G_deg (hp : 5 ≤ p) (c : Fin 6) (n : ℕ) (hn : n + 2 ≤ 6) :
    (blk6G (p := p) c n).natDegree = n ∧ (blk6G (p := p) c n).coeff n ≠ 0 := by
  have h24 : (24 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have key : cfOf (F := ZMod p) (s := 6) blk6GL 24 c n n ≠ 0 := by
    have : n ≤ 4 := by omega
    interval_cases n <;> fin_cases c <;> simp [cfOf, blk6GL, h24] <;> smooth_ne hp
  obtain ⟨h1, h2⟩ := sumX_natDegree (cfOf (F := ZMod p) (s := 6) blk6GL 24 c n) n key
  exact ⟨h1, by rw [blk6G, h2]; exact key⟩

set_option maxHeartbeats 8000000 in
/-- **The nets' form of `blk6dF`**: `F_n[i][c] = w̃_{ic} G_{c,n}(ỹ_{ic})` (`i ≠ c`), every prime `p ≥ 5`. -/
theorem blk6d_netsForm (hp : 5 ≤ p) : ∀ c i, i ≠ c → ∀ n, n + 2 ≤ 6 →
    blockF (F := ZMod p) blk6dF n i c = wNp i c * (blk6G c n).eval (yNp i c) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm3 : (-3 : ZMod p) ≠ 0 := neg_ne_zero.mpr h3
  have h4 : (4 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm4 : (-4 : ZMod p) ≠ 0 := neg_ne_zero.mpr h4
  have h6 : (6 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm6 : (-6 : ZMod p) ≠ 0 := neg_ne_zero.mpr h6
  have h8 : (8 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm8 : (-8 : ZMod p) ≠ 0 := neg_ne_zero.mpr h8
  have h9 : (9 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm9 : (-9 : ZMod p) ≠ 0 := neg_ne_zero.mpr h9
  have h12 : (12 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm12 : (-12 : ZMod p) ≠ 0 := neg_ne_zero.mpr h12
  have h16 : (16 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm16 : (-16 : ZMod p) ≠ 0 := neg_ne_zero.mpr h16
  have h18 : (18 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm18 : (-18 : ZMod p) ≠ 0 := neg_ne_zero.mpr h18
  have h24 : (24 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm24 : (-24 : ZMod p) ≠ 0 := neg_ne_zero.mpr h24
  have h27 : (27 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm27 : (-27 : ZMod p) ≠ 0 := neg_ne_zero.mpr h27
  have h32 : (32 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm32 : (-32 : ZMod p) ≠ 0 := neg_ne_zero.mpr h32
  have h36 : (36 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm36 : (-36 : ZMod p) ≠ 0 := neg_ne_zero.mpr h36
  have h48 : (48 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm48 : (-48 : ZMod p) ≠ 0 := neg_ne_zero.mpr h48
  have h54 : (54 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm54 : (-54 : ZMod p) ≠ 0 := neg_ne_zero.mpr h54
  have h64 : (64 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm64 : (-64 : ZMod p) ≠ 0 := neg_ne_zero.mpr h64
  have h72 : (72 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm72 : (-72 : ZMod p) ≠ 0 := neg_ne_zero.mpr h72
  have h81 : (81 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm81 : (-81 : ZMod p) ≠ 0 := neg_ne_zero.mpr h81
  have h96 : (96 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm96 : (-96 : ZMod p) ≠ 0 := neg_ne_zero.mpr h96
  have h108 : (108 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm108 : (-108 : ZMod p) ≠ 0 := neg_ne_zero.mpr h108
  have h128 : (128 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm128 : (-128 : ZMod p) ≠ 0 := neg_ne_zero.mpr h128
  have h144 : (144 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm144 : (-144 : ZMod p) ≠ 0 := neg_ne_zero.mpr h144
  have h162 : (162 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm162 : (-162 : ZMod p) ≠ 0 := neg_ne_zero.mpr h162
  have h192 : (192 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm192 : (-192 : ZMod p) ≠ 0 := neg_ne_zero.mpr h192
  have h216 : (216 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm216 : (-216 : ZMod p) ≠ 0 := neg_ne_zero.mpr h216
  have h243 : (243 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm243 : (-243 : ZMod p) ≠ 0 := neg_ne_zero.mpr h243
  have h256 : (256 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have hm256 : (-256 : ZMod p) ≠ 0 := neg_ne_zero.mpr h256
  intro c i hic n hn
  have : n ≤ 4 := by omega
  interval_cases n <;> fin_cases c <;> fin_cases i <;> simp at hic ⊢ <;>
    simp [blockF, blk6dF, wNp, yNp, blk6G, cfOf, blk6GL, Finset.sum_range_succ, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;>
    first
      | done
      | (norm_num <;> done)
      | (norm_num <;> field_simp <;> norm_num <;> done)
      | (norm_num <;> field_simp <;> ring_nf <;> done)
      | (field_simp <;> norm_num <;> done)

/-- **Reachability of `blk6dF`** (`def:block`) at the places `0, 1, 1/2, …, 1/5` with `v = (1, 1, 2, 3, 4, 5)`, every
prime `p ≥ 7`. -/
theorem blk6d_reach (hp : 7 ≤ p) :
    IsReachable (ustarA (p := p) 6) (ustarV 6) (blockF blk6dF) (fun c n => C (-sgC c) * (blk6G c n).comp (affC c)) :=
  reach_of_netsForm (by omega) _ blk6G (fun c n hn => blk6G_deg (by omega) c n hn) (blk6d_netsForm (by omega))

/-! ## The bound and the sequence -/

lemma blk6d_hq (hp : 125 ≤ p) : ((p : ℤ) - ((14 : ℕ) : ℤ) - 1) ^ 2 ≤ 2 * ((p : ℤ) - ((46 : ℕ) : ℤ) - 1) ^ 2 := by
  have : (125 : ℤ) ≤ p := by exact_mod_cast hp
  push_cast; nlinarith

/-- `LB(F) ≥ 1 - 15/p` for `blk6dF` at every prime `p ≥ 125` (sign-class argument, `sc_LB`), given the evaluation of
the checker at `P = 6367`. -/
theorem blk6d_LB_of_chk (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true)
    (hp : 125 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 15) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  suffices key : ((p : ℝ) - ((14 : ℕ) : ℝ) - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) by
    convert key using 2; push_cast; ring
  exact sc_LB (by norm_num) blk6dF blk6dM blk6d_hM blk6dB blk6d_hB 46 14 blk6d_rows.1 (by omega) (by norm_num)
    (blk6d_hq hp) (blk6d_signclass_of hchk) K e l h

/-- `LB(F) ≥ 1 - 15/p` for `blk6dF` at every prime `p ≥ 125` (unconditional; `lake build` only). -/
theorem blk6d_LB_proof (hp : 125 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 15) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) :=
  blk6d_LB_of_chk blk6d_chk hp K

/-- **The binding configuration at a deeper carry depth**: the axis step `e = 𝟏_c` with carry lengths `j + 1`
(`j + 2 ≤ s`, `j + 1 ≤ K`) has the term `(p - α - 1)/p` if `M^{(j)}[c][c] = -α` (`α < p`) and the other entries of
column `c` of `M^{(j)}` lie in `[-1, 1]` (`axis_term` is the case `j = 0`). -/
theorem axis_term_depth {s : ℕ} (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c) (c : Fin s) (j α : ℕ) (hj : j + 2 ≤ s)
    (hα : Mz j c c = -α) (hαp : α < p) (hcol : ∀ i, i ≠ c → |Mz j i c| ≤ 1) (K : ℕ) (hK : j + 1 ≤ K) :
    IsStep K (Pi.single c 1) (fun _ => j + 1) ∧
      Real.sqrt (∑ i, ((gapNum1 p ((Pi.single c (1 : ℤ) : Fin s → ℤ) i) (∑ c', (((Pi.single c (1 : ℤ) :
        Fin s → ℤ) c' : ℤ) : ZMod p) * ∑ n ∈ range (min ((fun _ => j + 1 : Fin s → ℕ) c') (s - 1)),
          blockF Fz n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - α - 1) / p := by
  refine ⟨⟨fun c' => ?_, ⟨c, by simp⟩, fun _ => ⟨Nat.succ_le_succ (Nat.zero_le j), hK⟩⟩, ?_⟩
  · by_cases h : c' = c
    · subst h; simp
    · simp [h]
  simp_rw [sig_cast hs Fz Mz hM (Pi.single c 1) (fun _ => j + 1) (fun _ => by omega)]
  have hsig : ∀ i, caSig Mz (Pi.single c 1) (fun _ => j + 1) i = Mz j i c := fun i => by
    unfold caSig
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp [show min (j + 1) (s - 1) - 1 = j by omega]
  have hgap : ∀ i, gapNum1 p ((Pi.single c (1 : ℤ) : Fin s → ℤ) i)
      ((caSig Mz (Pi.single c 1) (fun _ => j + 1) i : ℤ) : ZMod p) = if i = c then p - α - 1 else 0 := by
    intro i
    rw [hsig]
    by_cases hi : i = c
    · subst hi
      rw [if_pos rfl, Pi.single_eq_same, hα]
      have := gap_back (p := p) 1 (-α) (Or.inl rfl) (by simp) (by rw [abs_neg, Nat.abs_cast]; exact_mod_cast hαp)
      rw [abs_neg, Nat.abs_cast] at this
      omega
    · rw [if_neg hi, Pi.single_eq_of_ne hi]
      exact gap_zero_small _ (hcol i hi)
  simp_rw [hgap]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), if_pos rfl]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnn : (0 : ℝ) ≤ ((p : ℝ) - α - 1) / p := by
    apply div_nonneg _ hp0.le
    have : (α : ℝ) + 1 ≤ p := by exact_mod_cast hαp
    linarith
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  rw [Real.sqrt_sq hnn]

/-- **`LB(F) = 1 - 15/p` for `blk6dF`**, every prime `p ≥ 125` and every level `K ≥ 4`: every step has a term
`≥ 1 - 15/p`, and the axis step along the place `1/3` with carry length `4` attains it. -/
theorem blk6d_LB_eq_of_chk (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true)
    (hp : 125 ≤ p) (K : ℕ) (hK : 4 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 15) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 15) / p := by
  refine ⟨blk6d_LB_of_chk hchk hp K, ?_⟩
  obtain ⟨h1, h2⟩ := axis_term_depth (p := p) (by norm_num) blk6dF blk6dM blk6d_hM 3 3 14 (by norm_num)
    (by decide) (by omega) (by decide) K (by omega)
  refine ⟨_, _, h1, ?_⟩
  rw [h2]; push_cast; ring

/-- **The improved `s = 6` block-periodic sequence**: places `0, 1, 1/2, …, 1/5`, `v = (1, 1, 2, 3, 4, 5)`, the design
`blk6dF` (`U*_6` off the diagonal, `F_0[c][c] = -(3, 12, 13, 14, 13, 13)`). For every prime `p ≥ 125` and `θ ≠ 0`: a
digital `(0,6)`-sequence, the design relation at every `P_{36K}`, and `sep(P_{36K}) ≥ 1 - 15/p` (`U*_6`: `1 - 44/p`,
`p ≥ 219`). -/
theorem blk6d_block_of_chk (hchk : caCheck 6 (blk6dO0 :: blk6dO1 :: blk6dRest2) blk6dSt0 6367 14 = true)
    (hp : 125 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk6d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (6 * (6 * K)) →
        seqDigit (zcode p) (blk6d θ) x i (6 * K) =
          ∑ c, ∑ n ∈ range (6 - 1), blockF blk6dF n i c * seqDigit (zcode p) (blk6d θ) x c (6 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 6 (6 * K) (seqPoint (zcode p) (blk6d θ)) (((p : ℝ) - 15) / p) := by
  have h := reach_block (by norm_num) _ (ustarA_injective (p := p) (by omega)) _ (ustarV_ne (by omega)) blk6dF _
    (blk6d_reach (by omega)) θ hθ
  refine ⟨h.1, h.2.1, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 15) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have := h.2.2 K hK _ (blk6d_LB_of_chk hchk hp (6 * K))
  rwa [min_eq_right hLB1] at this

/-- **`LB(F) = 1 - 15/p` for `blk6dF`** (unconditional; `lake build` only), every prime `p ≥ 125`, every level `K ≥ 4`. -/
theorem blk6d_LB_eq (hp : 125 ≤ p) (K : ℕ) (hK : 4 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 15) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (6 - 1)), blockF blk6dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 15) / p :=
  blk6d_LB_eq_of_chk blk6d_chk hp K hK

/-- **The improved `s = 6` block-periodic sequence** (unconditional; `lake build` only: its closure contains the 121
kernel evaluations, compared one module per configuration): for every prime `p ≥ 125` and `θ ≠ 0`, a digital
`(0,6)`-sequence, the design relation at every `P_{36K}`, and `sep(P_{36K}) ≥ 1 - 15/p`. -/
theorem blk6d_block (hp : 125 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk6d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (6 * (6 * K)) →
        seqDigit (zcode p) (blk6d θ) x i (6 * K) =
          ∑ c, ∑ n ∈ range (6 - 1), blockF blk6dF n i c * seqDigit (zcode p) (blk6d θ) x c (6 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 6 (6 * K) (seqPoint (zcode p) (blk6d θ)) (((p : ℝ) - 15) / p) :=
  blk6d_block_of_chk blk6d_chk hp θ hθ

end GeoSeq
