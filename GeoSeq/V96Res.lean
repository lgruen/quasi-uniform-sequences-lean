/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Defs
public import GeoSeq.V94Thm

@[expose] public section

/-!
# GeoSeq stage V9-6 (part 1): block-periodic residue sequences, general facts (`def:block`, `thm:block`(i),(ii),
`thm:blocktwo`(i)–(iii), `prop:implied`)

Over any field, distinct places, `1 ≤ s ≤ ℓ`.

* Residue algebra: `locRes_add`, `locRes_C_mul`, `locRes_sum`, `locRes_cancel_unit` (a common unit factor),
  `locRes_cancel_pow` (`(z-a)^e` in the numerator lowers the pole order by `e`); `lagrange_one`
  (`∑_i w_i / w_i(a_i) = 1`) and `pf_res` (partial fractions `∑_i u_i/w'(a_i) = 1/w`, residue by residue).
* `blockNum_order`: every numerator vanishes to order exactly `ℓ-1-j` at its place (given this for the design
  numerators — for the instances a direct computation; in general it follows from reachability, not formalized);
  **`blockGen_t0`** (`thm:block`(i), `thm:blocktwo`(i)): a digital `(0,s)`-sequence.
* `blockDig_own`, `blockDig_zero` (the identity with the coefficient at infinity kept), **`blockGen_rel`**
  (`thm:block`(ii), `thm:blocktwo`(ii)): `y_{i,ℓK} = ∑_c ∑_{n ≤ s-2} F_n[i][c] y_{c,ℓK-1-n}` for `deg V < sℓK`, given the
  multiplier identities (a); `blockGen_skel` (`thm:blocktwo`(iii)); **`blockGen_implied`** (`prop:implied`).
-/

namespace GeoSeq

open Finset Polynomial

section Res
variable {F : Type*} [Field F]

lemma locRes_zero_k (a : F) (V U : F[X]) : locRes a 0 V U = 0 := by simp [locRes]

lemma locRes_add (a : F) (k : ℕ) (V W U : F[X]) :
    locRes a k (V + W) U = locRes a k V U + locRes a k W U := by
  unfold locRes
  split_ifs
  · simp
  · rw [map_add, Polynomial.coe_add, add_mul, map_add]

lemma locRes_C_mul (a r : F) (k : ℕ) (V U : F[X]) : locRes a k (C r * V) U = r * locRes a k V U := by
  unfold locRes
  split_ifs
  · simp
  · rw [taylor_mul, taylor_C, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, PowerSeries.coeff_C_mul]

lemma locRes_zero_num (a : F) (k : ℕ) (U : F[X]) : locRes a k 0 U = 0 := by
  have := locRes_C_mul a 0 k 0 U
  rwa [map_zero, zero_mul, zero_mul] at this

lemma locRes_sum {ι : Type*} (a : F) (k : ℕ) (U : F[X]) (t : Finset ι) (g : ι → F[X]) :
    locRes a k (∑ i ∈ t, g i) U = ∑ i ∈ t, locRes a k (g i) U := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [locRes_zero_num]
  | insert b t hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, locRes_add, ih]

/-- A common unit factor cancels: `Res_a(V A / ((z-a)^k A U)) = Res_a(V / ((z-a)^k U))`. -/
lemma locRes_cancel_unit (a : F) (k : ℕ) (V A U : F[X]) (hA : A.eval a ≠ 0) :
    locRes a k (V * A) (A * U) = locRes a k V U := by
  unfold locRes
  split_ifs
  · rfl
  · have hcA : PowerSeries.constantCoeff (taylor a A : PowerSeries F) ≠ 0 := by
      rw [constantCoeff_taylor]; exact hA
    rw [taylor_mul, taylor_mul, Polynomial.coe_mul, Polynomial.coe_mul, PowerSeries.mul_inv_rev]
    congr 1
    calc (taylor a V : PowerSeries F) * (taylor a A) * ((taylor a U : PowerSeries F)⁻¹ * (taylor a A : PowerSeries F)⁻¹)
        = (taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹ *
          ((taylor a A : PowerSeries F) * (taylor a A : PowerSeries F)⁻¹) := by ring
      _ = _ := by rw [PowerSeries.mul_inv_cancel _ hcA, mul_one]

/-- `(z-a)^e` in the numerator lowers the pole order by `e`. -/
lemma locRes_cancel_pow (a : F) (k e : ℕ) (V U : F[X]) :
    locRes a (k + e) (V * (X - C a) ^ e) U = locRes a k V U := by
  unfold locRes
  rw [taylor_mul, taylor_pow, taylor_X_sub_C, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos (rfl : (0 : ℕ) = 0)]
    split_ifs with he
    · rfl
    · rw [show (taylor a V : PowerSeries F) * PowerSeries.X ^ e * (taylor a U : PowerSeries F)⁻¹ =
          PowerSeries.X ^ e * ((taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹) by ring,
        PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · rw [if_neg (by omega), if_neg hk,
      show (taylor a V : PowerSeries F) * PowerSeries.X ^ e * (taylor a U : PowerSeries F)⁻¹ =
        PowerSeries.X ^ e * ((taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹) by ring,
      PowerSeries.coeff_X_pow_mul', if_pos (by omega), show k + e - 1 - e = k - 1 by omega]

variable {s : ℕ}

lemma wPoly_eq (a : Fin s → F) (c : Fin s) : wPoly a = (X - C (a c)) * wCo a c := by
  rw [wPoly, wCo]; exact (Finset.mul_prod_erase _ _ (mem_univ c)).symm

lemma wCo_eq (a : Fin s → F) {c i : Fin s} (h : i ≠ c) : wCo a c = (X - C (a i)) * wCoCo a c i := by
  rw [wCo, wCoCo]; exact (Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h, mem_univ i⟩)).symm

lemma wCoCo_comm (a : Fin s → F) (c i : Fin s) : wCoCo a c i = wCoCo a i c := by
  rw [wCoCo, wCoCo, Finset.erase_right_comm]

lemma wCoCo_eval_ne (a : Fin s → F) (ha : Function.Injective a) (c i : Fin s) :
    (wCoCo a c i).eval (a c) ≠ 0 := by
  rw [wCoCo, eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i' hi' => by
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact fun h => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi') (ha h).symm

lemma wCo_eval_other (a : Fin s → F) {c i : Fin s} (h : i ≠ c) : (wCo a c).eval (a i) = 0 := by
  rw [wCo_eq a h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

lemma natDegree_wCo (a : Fin s → F) (c : Fin s) : (wCo a c).natDegree = s - 1 := by
  have := placeCo_natDegree a (fun _ => 1) c
  rwa [placeCo_const, pow_one, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this

/-- Lagrange: `∑_i w_i / w_i(a_i) = 1` for distinct places (`w_i = ∏_{i' ≠ i} (z - a_{i'})`). -/
lemma lagrange_one (a : Fin s → F) (ha : Function.Injective a) (hs : 1 ≤ s) :
    ∑ i, C ((wCo a i).eval (a i))⁻¹ * wCo a i = 1 := by
  refine sub_eq_zero.mp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ha (fun j => ?_) ?_)
  · rw [eval_sub, eval_one, eval_finset_sum, Finset.sum_eq_single j]
    · rw [eval_mul, eval_C, inv_mul_cancel₀ (wCo_eval_ne a ha j), sub_self]
    · intro i _ hij; rw [eval_mul, wCo_eval_other a (Ne.symm hij), mul_zero]
    · intro h; exact absurd (mem_univ j) h
  · rw [Fintype.card_fin]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ (by rw [natDegree_one]; omega))
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := s - 1) fun i _ => ?_) (by omega)
    exact (natDegree_C_mul_le _ _).trans (natDegree_wCo a i).le

/-- Partial fractions residue by residue: `∑_i Res_{a_c}(V u_i w^{-N} dz) / w'(a_i) = Res_{a_c}(V w^{-N-1} dz)`. -/
theorem pf_res (a : Fin s → F) (ha : Function.Injective a) (hs : 1 ≤ s) (N : ℕ) (V : F[X]) (c : Fin s) :
    ∑ i, ((wCo a i).eval (a i))⁻¹ * resAt a (stagK i N) V c = resAt a (fun _ => N + 1) V c := by
  have hterm : ∀ i, resAt a (stagK i N) V c = locRes (a c) (N + 1) (V * wCo a i) (wCo a c ^ (N + 1)) := by
    intro i
    rw [resAt]
    by_cases h : i = c
    · subst h
      rw [placeCo_stagK_self, stagK, if_pos rfl, pow_succ', ← locRes_cancel_unit (a i) (N + 1) V (wCo a i)
        (wCo a i ^ N) (wCo_eval_ne a ha i)]
    · have e : wCo a c ^ (N + 1) = wCoCo a c i * ((X - C (a i)) * wCo a c ^ N) := by rw [wCo_eq a h]; ring
      rw [placeCo_stagK_ne a i c (Ne.symm h), stagK, if_neg (Ne.symm h), wCo_eq a (Ne.symm h), wCoCo_comm,
        show V * ((X - C (a c)) * wCoCo a c i) = (V * wCoCo a c i) * (X - C (a c)) ^ 1 by ring,
        locRes_cancel_pow, e, locRes_cancel_unit _ _ _ _ _ (wCoCo_eval_ne a ha c i)]
  simp_rw [hterm, ← locRes_C_mul]
  rw [← locRes_sum, resAt, placeCo_const]
  congr 1
  have hsum : ∑ i, C ((wCo a i).eval (a i))⁻¹ * (V * wCo a i) =
      V * ∑ i, C ((wCo a i).eval (a i))⁻¹ * wCo a i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, lagrange_one a ha hs, mul_one]

end Res

section Block
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
  (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F)

lemma blockDig_add (c : Fin s) (d : ℕ) (V W : F[X]) :
    blockDig a θ ℓ v Fd Nd v' c d (V + W) = blockDig a θ ℓ v Fd Nd v' c d V + blockDig a θ ℓ v Fd Nd v' c d W := by
  unfold blockDig; rw [add_mul, locRes_add, mul_add]

lemma blockDig_C_mul (c : Fin s) (d : ℕ) (r : F) (V : F[X]) :
    blockDig a θ ℓ v Fd Nd v' c d (C r * V) = r * blockDig a θ ℓ v Fd Nd v' c d V := by
  unfold blockDig; rw [mul_assoc, locRes_C_mul]; ring

/-- The digits of the point with index digits `f_0, …, f_{m-1}` are `blockDig` of the index polynomial. -/
lemma blockGen_vecPoly (c : Fin s) (d : ℕ) (f : ℕ → F) (m : ℕ) :
    ∑ j ∈ range m, blockGen a θ ℓ v Fd Nd v' c d j * f j = blockDig a θ ℓ v Fd Nd v' c d (vecPoly f m) := by
  induction m with
  | zero => simp [vecPoly, blockDig, locRes_zero_num]
  | succ m ih =>
    have hv : vecPoly f (m + 1) = vecPoly f m + C (f m) * X ^ m := by simp [vecPoly, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih, hv, blockDig_add, blockDig_C_mul]
    simp only [blockGen]; ring

variable {a}

/-- The order of vanishing of the numerators (`proof of thm:block`(i)): if every design numerator `N_{c,ℓ-1-n}`
(`n ≤ s-2`) is `(z - a_c)^n` times a unit at `a_c`, then every numerator `N_{c,j}`, `j < ℓ`, is `(z - a_c)^{ℓ-1-j}` times
a unit at `a_c`. -/
theorem blockNum_order (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hv : ∀ c, v c ≠ 0)
    (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (c : Fin s) (j : ℕ) (hj : j < ℓ) :
    ∃ N', blockNum a θ ℓ v Fd Nd v' c j = (X - C (a c)) ^ (ℓ - 1 - j) * N' ∧ N'.eval (a c) ≠ 0 := by
  have hw := wPoly_eq a c
  have hwc := wCo_eval_ne a ha c
  set Y : F[X] := X - C (a c) with hY
  unfold blockNum
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl]
    obtain ⟨L, hL⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
    set S := ∑ n ∈ range (s - 1), C (Fd n c c) * Nd c (ℓ - 1 - n)
    refine ⟨C θ⁻¹ * (C (v c)⁻¹ * wCo a c ^ (ℓ + 1) + Y * wCo a c ^ ℓ * S), ?_, ?_⟩
    · rw [hw, hL]; simp only [Nat.add_sub_cancel, Nat.sub_zero]; ring
    · rw [eval_mul, eval_C, eval_add, eval_mul, eval_mul, eval_C, eval_mul, eval_sub, eval_X, eval_C, sub_self,
        zero_mul, zero_mul, add_zero, eval_pow]
      exact mul_ne_zero (inv_ne_zero hθ) (mul_ne_zero (inv_ne_zero (hv c)) (pow_ne_zero _ hwc))
  · rw [if_neg h0]
    by_cases hsk : j ≤ ℓ - s
    · rw [if_pos hsk]
      refine ⟨C (v' c)⁻¹ * wCo a c ^ (ℓ - j), ?_, ?_⟩
      · rw [hw, show ℓ - j = (ℓ - 1 - j) + 1 by omega]; ring
      · rw [eval_mul, eval_C, eval_pow]; exact mul_ne_zero (inv_ne_zero (hv' c)) (pow_ne_zero _ hwc)
    · rw [if_neg hsk]
      obtain ⟨N', hN', hN'0⟩ := hNd c (ℓ - 1 - j) (by omega)
      rw [show ℓ - 1 - (ℓ - 1 - j) = j by omega] at hN'
      exact ⟨N', hN', hN'0⟩

/-- **`thm:block`(i)**, **`thm:blocktwo`(i)**: the block-periodic residue sequence is a digital `(0,s)`-sequence. -/
theorem blockGen_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q)
    (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s) (hv : ∀ c, v c ≠ 0)
    (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0) :
    IsSeq0 D (blockGen a θ ℓ v Fd Nd v') := by
  have hℓ : 0 < ℓ := by omega
  have hrow : ∀ c d, ∃ L : ℕ → F, (∀ k, blockGen a θ ℓ v Fd Nd v' c d k =
      ∑ t ∈ range (d + 1), L t * pas (a c) t k) ∧ L d ≠ 0 := by
    intro c d
    obtain ⟨N', hN', hN'0⟩ := blockNum_order θ ℓ v Fd Nd v' ha hθ hsℓ hv hv' hNd c (d % ℓ)
      (Nat.mod_lt _ hℓ)
    have hU : (wCo a c ^ (ℓ * (d / ℓ + 1) + 1)).eval (a c) ≠ 0 := by
      rw [eval_pow]; exact pow_ne_zero _ (wCo_eval_ne a ha c)
    have hk : ℓ * (d / ℓ + 1) = (d + 1) + (ℓ - 1 - d % ℓ) := by
      have := Nat.div_add_mod d ℓ; have := Nat.mod_lt d hℓ
      rw [mul_add, mul_one]; omega
    have e1 : ∀ W : F[X], locRes (a c) (ℓ * (d / ℓ + 1)) (W * blockNum a θ ℓ v Fd Nd v' c (d % ℓ))
        (wCo a c ^ (ℓ * (d / ℓ + 1) + 1)) = locRes (a c) (d + 1) (W * N') (wCo a c ^ (ℓ * (d / ℓ + 1) + 1)) := by
      intro W
      rw [hN', ← locRes_cancel_pow (a c) (d + 1) (ℓ - 1 - d % ℓ) (W * N'), ← hk]
      congr 1; ring
    refine ⟨fun t => θ ^ (d / ℓ + 1) * PowerSeries.coeff (d - t) ((taylor (a c) N' : PowerSeries F) *
      (taylor (a c) (wCo a c ^ (ℓ * (d / ℓ + 1) + 1)) : PowerSeries F)⁻¹), fun k => ?_, ?_⟩
    · simp only [blockGen, blockDig]
      rw [e1, locRes, if_neg (Nat.succ_ne_zero d), Nat.add_sub_cancel, taylor_mul, Polynomial.coe_mul,
        mul_assoc, coeff_mul_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.coeff_coe, coeff_taylor_X_pow]; ring
    · simp only [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        PowerSeries.constantCoeff_inv, constantCoeff_taylor]
      exact mul_ne_zero (pow_ne_zero _ hθ) (mul_ne_zero hN'0 (inv_ne_zero hU))
  choose L hL hLd using hrow
  have hgen : blockGen a θ ℓ v Fd Nd v' = scrGen a L := by
    funext c d k; rw [hL c d k, scrGen]
  rw [hgen]
  exact t0 D a ha L hLd

variable (a)

lemma stagK_sum' (i : Fin s) (N : ℕ) : ∑ c, stagK i N c = s * N + 1 := stagK_sum i N

/-- The identity behind `thm:block`(ii) and `prop:implied` (`K ≥ 1`, any `V`): with the multiplier identities (a)
`u_i = -v_i ∑_n F_n[i][c] φ_{c,ℓ-1-n}` (`i ≠ c`), `y_{i,ℓK}(V) = ∑_c ∑_{n ≤ s-2} F_n[i][c] y_{c,ℓK-1-n}(V) +
θ^K v_i^{-1} ∑_c Res_{a_c}(V u_i w^{-ℓK} dz)` (the last sum is `[z^{-1}]` of `θ^K V u_i w^{-ℓK}`, `res_thm`). -/
theorem blockDig_own (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : Fin s) (V : F[X]) :
    blockDig a θ ℓ v Fd Nd v' i (ℓ * K) V =
      ∑ c, ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) V +
        θ ^ K * (v i)⁻¹ * ∑ c, resAt a (stagK i (ℓ * K)) V c := by
  have hℓ : 0 < ℓ := by omega
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  have hwi := wPoly_eq a i
  have hwie := wCo_eval_ne a ha i
  have hKK : (L + 1) * K = (L + 1) * (K - 1) + (L + 1) := by
    rw [show (L + 1) * (K - 1) + (L + 1) = (L + 1) * (K - 1 + 1) by ring]; congr 1; omega
  -- the design digits `ℓK - 1 - n`
  have hdes : ∀ c n, n + 2 ≤ s → blockDig a θ (L + 1) v Fd Nd v' c ((L + 1) * K - 1 - n) V =
      θ ^ K * locRes (a c) ((L + 1) * K) (V * Nd c (L + 1 - 1 - n)) (wCo a c ^ ((L + 1) * K + 1)) := by
    intro c n hn
    have hx : (L + 1) * K - 1 - n = (L - n) + (L + 1) * (K - 1) := by omega
    have hq : ((L + 1) * K - 1 - n) / (L + 1) = K - 1 := by
      rw [hx, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
    have hr : ((L + 1) * K - 1 - n) % (L + 1) = L + 1 - 1 - n := by
      rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; omega
    unfold blockDig
    rw [hq, hr, show K - 1 + 1 = K by omega, blockNum, if_neg (by omega), if_neg (by omega)]
  -- the own digit `ℓK`
  have hq0 : (L + 1) * K / (L + 1) = K := by rw [Nat.mul_div_cancel_left _ (by omega)]
  have hr0 : (L + 1) * K % (L + 1) = 0 := Nat.mul_mod_right _ _
  set S := ∑ n ∈ range (s - 1), C (Fd n i i) * Nd i (L + 1 - 1 - n) with hS
  have hA : locRes (a i) ((L + 1) * (K + 1)) (V * wPoly a ^ (L + 1 - 1) * wCo a i ^ 2)
      (wCo a i ^ ((L + 1) * (K + 1) + 1)) = resAt a (stagK i ((L + 1) * K)) V i := by
    rw [resAt, placeCo_stagK_self, stagK, if_pos rfl, hwi, Nat.add_sub_cancel,
      show V * ((X - C (a i)) * wCo a i) ^ L * wCo a i ^ 2 = (V * wCo a i ^ (L + 2)) * (X - C (a i)) ^ L by rw [mul_pow]; ring,
      show (L + 1) * (K + 1) = ((L + 1) * K + 1) + L by ring,
      show wCo a i ^ ((L + 1) * K + 1 + L + 1) = wCo a i ^ (L + 2) * wCo a i ^ ((L + 1) * K) by
        rw [← pow_add]; congr 1; ring,
      locRes_cancel_pow, locRes_cancel_unit _ _ _ _ _ (by rw [eval_pow]; exact pow_ne_zero _ hwie)]
  have hB : ∀ n, locRes (a i) ((L + 1) * (K + 1)) (V * wPoly a ^ (L + 1) * Nd i (L + 1 - 1 - n))
      (wCo a i ^ ((L + 1) * (K + 1) + 1)) =
      locRes (a i) ((L + 1) * K) (V * Nd i (L + 1 - 1 - n)) (wCo a i ^ ((L + 1) * K + 1)) := by
    intro n
    rw [hwi, show V * ((X - C (a i)) * wCo a i) ^ (L + 1) * Nd i (L + 1 - 1 - n) =
        (V * Nd i (L + 1 - 1 - n) * wCo a i ^ (L + 1)) * (X - C (a i)) ^ (L + 1) by rw [mul_pow]; ring,
      show (L + 1) * (K + 1) = (L + 1) * K + (L + 1) by ring, locRes_cancel_pow,
      show wCo a i ^ ((L + 1) * K + (L + 1) + 1) = wCo a i ^ (L + 1) * wCo a i ^ ((L + 1) * K + 1) by
        rw [← pow_add]; congr 1; ring,
      locRes_cancel_unit _ _ _ _ _ (by rw [eval_pow]; exact pow_ne_zero _ hwie)]
  have hθK : θ ^ (K + 1) * θ⁻¹ = θ ^ K := by rw [pow_succ, mul_assoc, mul_inv_cancel₀ hθ, mul_one]
  have hL0 : blockDig a θ (L + 1) v Fd Nd v' i ((L + 1) * K) V = θ ^ (K + 1) *
      locRes (a i) ((L + 1) * (K + 1)) (V * blockNum a θ (L + 1) v Fd Nd v' i 0)
        (wCo a i ^ ((L + 1) * (K + 1) + 1)) := by
    unfold blockDig; rw [hq0, hr0]
  have hVN : V * blockNum a θ (L + 1) v Fd Nd v' i 0 =
      C θ⁻¹ * (C (v i)⁻¹ * (V * wPoly a ^ (L + 1 - 1) * wCo a i ^ 2)) +
        C θ⁻¹ * ∑ n ∈ range (s - 1), C (Fd n i i) * (V * wPoly a ^ (L + 1) * Nd i (L + 1 - 1 - n)) := by
    have h1 : V * wPoly a ^ (L + 1) * S =
        ∑ n ∈ range (s - 1), C (Fd n i i) * (V * wPoly a ^ (L + 1) * Nd i (L + 1 - 1 - n)) := by
      rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    rw [← h1, blockNum, if_pos rfl, ← hS]; ring
  have hown : blockDig a θ (L + 1) v Fd Nd v' i ((L + 1) * K) V =
      θ ^ K * (v i)⁻¹ * resAt a (stagK i ((L + 1) * K)) V i +
        ∑ n ∈ range (s - 1), Fd n i i * blockDig a θ (L + 1) v Fd Nd v' i ((L + 1) * K - 1 - n) V := by
    rw [hL0, hVN, locRes_add, locRes_C_mul, locRes_C_mul, locRes_C_mul, hA, locRes_sum]
    simp_rw [locRes_C_mul, hB]
    rw [mul_add, ← mul_assoc, ← mul_assoc, hθK, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hdes i n (by have := Finset.mem_range.mp hn; omega)]
    rw [← mul_assoc, ← mul_assoc, hθK]; ring
  have hcross : ∀ c, c ≠ i → ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ (L + 1) v Fd Nd v' c ((L + 1) * K - 1 - n) V
      = -(θ ^ K * (v i)⁻¹ * resAt a (stagK i ((L + 1) * K)) V c) := by
    intro c hci
    have hsum : ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (L + 1 - 1 - n) = -C (v i)⁻¹ * wCoCo a c i := by
      rw [hrel c i (Ne.symm hci), ← mul_assoc, neg_mul_neg, ← map_mul, inv_mul_cancel₀ (hv i), map_one, one_mul]
    have e : wCo a c ^ ((L + 1) * K + 1) = wCoCo a c i * ((X - C (a i)) * wCo a c ^ ((L + 1) * K)) := by
      rw [pow_succ, wCo_eq a (Ne.symm hci), mul_pow]; ring
    calc ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ (L + 1) v Fd Nd v' c ((L + 1) * K - 1 - n) V
        = θ ^ K * locRes (a c) ((L + 1) * K) (∑ n ∈ range (s - 1), C (Fd n i c) * (V * Nd c (L + 1 - 1 - n)))
            (wCo a c ^ ((L + 1) * K + 1)) := by
          rw [locRes_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hdes c n (by have := Finset.mem_range.mp hn; omega), locRes_C_mul]; ring
      _ = θ ^ K * locRes (a c) ((L + 1) * K) (C (-(v i)⁻¹) * (V * wCoCo a c i))
            (wCo a c ^ ((L + 1) * K + 1)) := by
          congr 2
          rw [show ∑ n ∈ range (s - 1), C (Fd n i c) * (V * Nd c (L + 1 - 1 - n)) =
            V * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (L + 1 - 1 - n) by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring, hsum, map_neg]
          ring
      _ = _ := by
          rw [locRes_C_mul, e, locRes_cancel_unit _ _ _ _ _ (wCoCo_eval_ne a ha c i), resAt,
            placeCo_stagK_ne a i c hci, stagK, if_neg hci]
          ring
  rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase (univ : Finset (Fin s)) _ (mem_univ i),
    hown, Finset.sum_congr rfl fun c hc => hcross c (Finset.ne_of_mem_erase hc), Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  ring

/-- `blockDig_own` at `K = 0`: digit `0` is `y_{i,0}(V) = v_i^{-1} Res_{a_i}(V u_i dz) = v_i^{-1} V(a_i)`, written with
the residues of `V u_i` at all places (only `a_i` contributes). -/
theorem blockDig_zero (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s) (i : Fin s)
    (V : F[X]) :
    blockDig a θ ℓ v Fd Nd v' i 0 V = (v i)⁻¹ * ∑ c, resAt a (stagK i 0) V c := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  have hwi := wPoly_eq a i
  have hwie := wCo_eval_ne a ha i
  rw [Finset.sum_eq_single i (fun c _ hc => by
      rw [resAt, stagK, if_neg hc, locRes_zero_k]) (by simp)]
  unfold blockDig
  simp only [Nat.zero_div, Nat.zero_mod, zero_add, pow_one, mul_one]
  rw [blockNum, if_pos rfl]
  have h1 : V * (C θ⁻¹ * (C (v i)⁻¹ * wPoly a ^ (L + 1 - 1) * wCo a i ^ 2 + wPoly a ^ (L + 1) *
      ∑ n ∈ range (s - 1), C (Fd n i i) * Nd i (L + 1 - 1 - n))) =
      C θ⁻¹ * (C (v i)⁻¹ * ((V * wCo a i ^ (L + 2)) * (X - C (a i)) ^ L)) +
        C θ⁻¹ * ((V * wCo a i ^ (L + 1) * ∑ n ∈ range (s - 1), C (Fd n i i) * Nd i (L + 1 - 1 - n)) *
          (X - C (a i)) ^ (L + 1)) := by
    rw [hwi, Nat.add_sub_cancel, mul_pow, mul_pow]; ring
  have t1 := locRes_cancel_pow (a i) 1 L (V * wCo a i ^ (L + 2)) (wCo a i ^ (L + 1 + 1))
  rw [show 1 + L = L + 1 by ring] at t1
  have t2 := locRes_cancel_pow (a i) 0 (L + 1)
    (V * wCo a i ^ (L + 1) * ∑ n ∈ range (s - 1), C (Fd n i i) * Nd i (L + 1 - 1 - n)) (wCo a i ^ (L + 1 + 1))
  rw [zero_add, locRes_zero_k] at t2
  have t3 := locRes_cancel_unit (a i) 1 V (wCo a i ^ (L + 2)) 1 (by rw [eval_pow]; exact pow_ne_zero _ hwie)
  rw [mul_one, show L + 2 = L + 1 + 1 by ring] at t3
  rw [h1, locRes_add, locRes_C_mul, locRes_C_mul, locRes_C_mul, t1, t2, mul_zero, add_zero, t3, resAt,
    placeCo_stagK_self, stagK, if_pos rfl, pow_zero]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hθ, one_mul]


/-- **`thm:block`(ii)**, **`thm:blocktwo`(ii)**: for `K ≥ 1`, every coordinate `i` and `deg V < m ≤ sℓK`, the
geometric digit follows the design exactly: `y_{i,ℓK}(V) = ∑_c ∑_{n ≤ s-2} F_n[i][c] y_{c,ℓK-1-n}(V)`. -/
theorem blockGen_rel (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : Fin s) (f : ℕ → F) (m : ℕ) (hm : m ≤ s * (ℓ * K)) :
    blockDig a θ ℓ v Fd Nd v' i (ℓ * K) (vecPoly f m) =
      ∑ c, ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) (vecPoly f m) := by
  have hpos : 1 ≤ s * (ℓ * K) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega)))
  rw [blockDig_own a θ ℓ v Fd Nd v' ha hθ hsℓ hs hrel hv K hK i, res_thm_zero a ha _ _ (by
    rw [stagK_sum]; have := vecPoly_natDegree f m; omega), mul_zero, add_zero]

/-- `thm:block`(ii) for the points: for every index `x < q^{sℓK}` (the full level `P_{sℓK}`). -/
theorem blockGen_rel_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (ha : Function.Injective a) (hθ : θ ≠ 0)
    (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : Fin s) (x : ℕ) (hx : x < q ^ (s * (ℓ * K))) :
    seqDigit D (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) =
      ∑ c, ∑ n ∈ range (s - 1), Fd n i c * seqDigit D (blockGen a θ ℓ v Fd Nd v') x c (ℓ * K - 1 - n) := by
  have hdig : ∀ c d, seqDigit D (blockGen a θ ℓ v Fd Nd v') x c d =
      blockDig a θ ℓ v Fd Nd v' c d (vecPoly (fun j => idxDigit D x j) (s * (ℓ * K))) := fun c d => by
    rw [seqDigit_eq_range D _ x c _ _ fun j hj => idxDigit_eq_zero D x j
      (digit_high x j (lt_of_lt_of_le hx (Nat.pow_le_pow_right (NeZero.pos q) hj))), blockGen_vecPoly]
  simp_rw [hdig]
  exact blockGen_rel a θ ℓ v Fd Nd v' ha hθ hsℓ hs hrel hv K hK i _ _ le_rfl

/-- **`thm:blocktwo`(iii)**: with `ℓ > s`, for `T = ℓn + j`, `1 ≤ j ≤ ℓ - s`, and `deg V < m`, `m + 1 ≤ s(T+1)`:
`∑_c v'_c y_{c,T}(V) = 0` (the skeleton relation of `lem:residue-rel` at level `T + 1` with the check vector `v'`). -/
theorem blockGen_skel (ha : Function.Injective a) (hv' : ∀ c, v' c ≠ 0) (n j : ℕ) (hj1 : 1 ≤ j)
    (hj : j + s ≤ ℓ) (hs : 1 ≤ s) (f : ℕ → F) (m : ℕ) (hm : m + 1 ≤ s * (ℓ * n + j + 1)) :
    ∑ c, v' c * blockDig a θ ℓ v Fd Nd v' c (ℓ * n + j) (vecPoly f m) = 0 := by
  have hℓ : 0 < ℓ := by omega
  have hq : (ℓ * n + j) / ℓ = n := by
    rw [add_comm, Nat.add_mul_div_left _ _ hℓ, Nat.div_eq_of_lt (by omega), zero_add]
  have hr : (ℓ * n + j) % ℓ = j := by rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hterm : ∀ c, v' c * blockDig a θ ℓ v Fd Nd v' c (ℓ * n + j) (vecPoly f m) =
      θ ^ (n + 1) * resAt a (fun _ => ℓ * n + j + 1) (vecPoly f m) c := by
    intro c
    have hwc := wCo_eval_ne a ha c
    unfold blockDig
    rw [hq, hr, blockNum, if_neg (by omega), if_pos (by omega), wPoly_eq a c, resAt, placeCo_const,
      show vecPoly f m * (C (v' c)⁻¹ * ((X - C (a c)) * wCo a c) ^ (ℓ - 1 - j) * wCo a c) =
        C (v' c)⁻¹ * ((vecPoly f m * wCo a c ^ (ℓ - j)) * (X - C (a c)) ^ (ℓ - 1 - j)) by
          rw [mul_pow, show ℓ - j = (ℓ - 1 - j) + 1 by omega, pow_succ]; ring,
      locRes_C_mul, show ℓ * (n + 1) = (ℓ * n + j + 1) + (ℓ - 1 - j) by
        rw [mul_add, mul_one]; omega, locRes_cancel_pow,
      show wCo a c ^ (ℓ * n + j + 1 + (ℓ - 1 - j) + 1) = wCo a c ^ (ℓ - j) * wCo a c ^ (ℓ * n + j + 1) by
        rw [← pow_add]; congr 1; omega,
      locRes_cancel_unit _ _ _ _ _ (by rw [eval_pow]; exact pow_ne_zero _ hwc)]
    rw [← mul_assoc, mul_comm (v' c), mul_assoc, ← mul_assoc (v' c), mul_inv_cancel₀ (hv' c), one_mul]
  simp_rw [hterm]
  have h2 : 2 ≤ s * (ℓ * n + j + 1) := le_trans (by omega : 2 ≤ ℓ * n + j + 1) (Nat.le_mul_of_pos_left _ hs)
  rw [← Finset.mul_sum, res_thm_zero a ha _ _ (by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; have := vecPoly_natDegree f m; omega),
    mul_zero]

/-- **`prop:implied`**: if `v̄_i = ξ v_i / w'(a_i)` and `v̄ᵀ F_n ≡ 0` for every `n ≤ s - 2`, then
`∑_i v̄_i y_{i,ℓK}(V) = 0` for every `K ≥ 0` and `deg V < m`, `m + 1 ≤ s(ℓK + 1)` (the skeleton relation with check vector
`v̄` at the level `s(ℓK+1) - 1`). -/
theorem blockGen_implied (ha : Function.Injective a) (hθ : θ ≠ 0) (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (vb : Fin s → F) (ξ : F) (hvb : ∀ i, vb i = ξ * v i / (wCo a i).eval (a i))
    (hF : ∀ n c, n + 2 ≤ s → ∑ i, vb i * Fd n i c = 0) (K : ℕ) (f : ℕ → F) (m : ℕ)
    (hm : m + 1 ≤ s * (ℓ * K + 1)) :
    ∑ i, vb i * blockDig a θ ℓ v Fd Nd v' i (ℓ * K) (vecPoly f m) = 0 := by
  have hs : 1 ≤ s := by omega
  set V := vecPoly f m
  have hcoef : ∀ i, vb i * (v i)⁻¹ = ξ * ((wCo a i).eval (a i))⁻¹ := fun i => by
    rw [hvb i]; field_simp [hv i]
  have hpf : ∑ i, vb i * (v i)⁻¹ * ∑ c, resAt a (stagK i (ℓ * K)) V c = 0 := by
    have h1 : ∀ i, vb i * (v i)⁻¹ * ∑ c, resAt a (stagK i (ℓ * K)) V c =
        ξ * ∑ c, ((wCo a i).eval (a i))⁻¹ * resAt a (stagK i (ℓ * K)) V c := fun i => by
      rw [hcoef, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum, Finset.sum_comm]
    simp_rw [pf_res a ha hs]
    have h2 : 2 ≤ s * (ℓ * K + 1) := le_trans hs2 (Nat.le_mul_of_pos_right _ (by omega))
    rw [res_thm_zero a ha _ _ (by
      rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      have : V.natDegree ≤ m - 1 := vecPoly_natDegree f m
      omega),
      mul_zero]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp only [mul_zero]
    simp_rw [blockDig_zero a θ ℓ v Fd Nd v' ha hθ hsℓ hs]
    simp only [mul_zero] at hpf
    rw [← hpf]; exact Finset.sum_congr rfl fun i _ => by ring
  · simp_rw [blockDig_own a θ ℓ v Fd Nd v' ha hθ hsℓ hs hrel hv K hK]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h1 : ∑ i, vb i * ∑ c, ∑ n ∈ range (s - 1), Fd n i c * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) V = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [show ∑ i, vb i * (Fd n i c * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) V) =
        (∑ i, vb i * Fd n i c) * blockDig a θ ℓ v Fd Nd v' c (ℓ * K - 1 - n) V by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
        hF n c (by have := Finset.mem_range.mp hn; omega), zero_mul]
    rw [h1, zero_add]
    rw [show ∑ i, vb i * (θ ^ K * (v i)⁻¹ * ∑ c, resAt a (stagK i (ℓ * K)) V c) =
      θ ^ K * ∑ i, vb i * (v i)⁻¹ * ∑ c, resAt a (stagK i (ℓ * K)) V c by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hpf, mul_zero]

end Block

end GeoSeq
