/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs

@[expose] public section

/-!
# GeoSeq stage V9-1: the residue identity (`lem:resform` (a), (c))

* `res_thm` (**`lem:resform`(c)**, residue theorem): for distinct places, every
  `F = V / ∏_c (z - a_c)^{k_c}` has `∑_c Res_{a_c}(F dz) = [z^{-1}] F`; `res_thm_of_deg` (the coefficient
  at `∞` is `[z^{M-1}] V` when `deg V < M`), `res_thm_zero` (the sum vanishes when `deg V ≤ M - 2`).
  Route (the research notes, a polynomial CRT argument instead of the paper's partial fractions): at
  each place the truncation `r_c` of the local series `V(a_c + t) · U_c(a_c + t)^{-1}` below `t^{k_c}`
  satisfies `V ≡ r_c U_c (mod (z - a_c)^{k_c})`, `deg r_c < k_c`, and its top coefficient is the residue
  (`locPart_*`). Then `V - ∑_c r_c U_c` is divisible by every `(z - a_c)^{k_c}`, hence by their product
  `D`, and `∑_c r_c U_c` has degree `< deg D`, so it is the remainder `V mod D`; its coefficient of
  `z^{M-1}` is `∑_c [z^{k_c - 1}] r_c = ∑_c Res_{a_c}`.
* `scrGen_res` (**`lem:resform`(a)**): for every scramble `L`, digit `n` of coordinate `c` is
  `∑_{k ≤ n} L_c[n][k] Res_{a_c}(V (z - a_c)^{-k-1} dz)`, i.e. the residue of `V` against the polar
  differential `η_{c,n} = ∑_{k ≤ n} L_c[n][k] (z - a_c)^{-k-1} dz` (`scrGen_res_polar`: one residue,
  `η_{c,n} = P_{c,n}(z) (z - a_c)^{-n-1} dz` with `P_{c,n} = ∑_{k ≤ n} L_c[n][k] (z - a_c)^{n-k}`
  (`polarNum`), of exact pole order `n + 1` iff `L_c[n][n] ≠ 0`, `polarNum_eval`). The converse of (a) (every family of polar
  differentials defines a scramble) is the definition `scrGen`.
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F]

/-! ## Taylor shifts, divisibility, truncation -/

lemma taylor_X_sub_C (a : F) : taylor a (X - C a) = X := by
  simp [taylor_X, taylor_C]

lemma taylor_neg_taylor (a : F) (f : F[X]) : taylor (-a) (taylor a f) = f := by
  rw [taylor_taylor, neg_add_cancel, taylor_zero]

lemma taylor_taylor_neg (a : F) (f : F[X]) : taylor a (taylor (-a) f) = f := by
  rw [taylor_taylor, add_neg_cancel, taylor_zero]

/-- `(z - a)^k ∣ f` iff the first `k` Taylor coefficients of `f` at `a` vanish. -/
lemma X_sub_C_pow_dvd_iff (a : F) (k : ℕ) (f : F[X]) :
    (X - C a) ^ k ∣ f ↔ ∀ j < k, (taylor a f).coeff j = 0 := by
  rw [← X_pow_dvd_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨taylor a g, by rw [taylor_mul, taylor_pow, taylor_X_sub_C]⟩
  · rintro ⟨g, hg⟩
    refine ⟨taylor (-a) g, ?_⟩
    have := congrArg (taylor (-a)) hg
    rw [taylor_neg_taylor, taylor_mul, taylor_pow, taylor_X, map_neg, ← sub_eq_add_neg] at this
    exact this

/-- The coefficient of `z^m` is invariant under a Taylor shift when `deg f ≤ m`. -/
lemma taylor_coeff_top (r : F) (f : F[X]) (m : ℕ) (hf : f.natDegree ≤ m) :
    (taylor r f).coeff m = f.coeff m := by
  rcases hf.lt_or_eq with h | h
  · rw [coeff_eq_zero_of_natDegree_lt h, coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_taylor])]
  · subst h
    have h1 := leadingCoeff_taylor (r := r) (f := f)
    rwa [leadingCoeff, natDegree_taylor, leadingCoeff] at h1

lemma constantCoeff_taylor (a : F) (U : F[X]) :
    PowerSeries.constantCoeff (taylor a U : PowerSeries F) = U.eval a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, taylor_coeff_zero]

/-- The local part of `V / ((z - a)^k U)` at `a`: the polynomial `r` of degree `< k` with
`r(a + t) = V(a + t) U(a + t)^{-1} mod t^k`. -/
noncomputable def locPart (a : F) (k : ℕ) (V U : F[X]) : F[X] :=
  taylor (-a) (PowerSeries.trunc k ((taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹))

lemma locPart_natDegree (a : F) (k : ℕ) (V U : F[X]) (hk : 1 ≤ k) :
    (locPart a k V U).natDegree ≤ k - 1 := by
  rw [locPart, natDegree_taylor]
  have := PowerSeries.natDegree_trunc_lt
    ((taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹) (k - 1)
  rw [Nat.sub_add_cancel hk] at this
  omega

lemma locPart_zero (a : F) (V U : F[X]) : locPart a 0 V U = 0 := by
  simp [locPart]

lemma locPart_coeff_top (a : F) (k : ℕ) (V U : F[X]) (hk : 1 ≤ k) :
    (locPart a k V U).coeff (k - 1) = locRes a k V U := by
  have hdeg := locPart_natDegree a k V U hk
  rw [locPart, natDegree_taylor] at hdeg
  rw [locPart, taylor_coeff_top _ _ _ hdeg, PowerSeries.coeff_trunc, locRes]
  simp only [show k - 1 < k by omega, show k ≠ 0 by omega, ite_true, ite_false]

lemma locPart_dvd (a : F) (k : ℕ) (V U : F[X]) (hU : U.eval a ≠ 0) :
    (X - C a) ^ k ∣ V - locPart a k V U * U := by
  rw [X_sub_C_pow_dvd_iff]
  intro j hj
  set S : PowerSeries F := (taylor a V : PowerSeries F) * (taylor a U : PowerSeries F)⁻¹ with hS
  set T : F[X] := PowerSeries.trunc k S with hT
  have hTa : taylor a (locPart a k V U) = T := taylor_taylor_neg a T
  have hU0 : PowerSeries.constantCoeff (taylor a U : PowerSeries F) ≠ 0 := by
    rwa [constantCoeff_taylor]
  have hSU : S * (taylor a U : PowerSeries F) = (taylor a V : PowerSeries F) := by
    rw [hS, mul_assoc, PowerSeries.inv_mul_cancel _ hU0, mul_one]
  have hTdeg : T.natDegree < k := by
    have := PowerSeries.natDegree_trunc_lt S (k - 1)
    rwa [Nat.sub_add_cancel (show 1 ≤ k by omega)] at this
  have key : PowerSeries.coeff j (S * (taylor a U : PowerSeries F)) =
      PowerSeries.coeff j ((T : PowerSeries F) * (taylor a U : PowerSeries F)) := by
    rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc S _ hj]
    conv_rhs => rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc (T : PowerSeries F) _ hj,
      PowerSeries.trunc_coe_eq_self hTdeg]
  rw [map_sub, taylor_mul, hTa, ← Polynomial.coeff_coe, Polynomial.coe_sub, Polynomial.coe_mul,
    map_sub, ← hSU, key, sub_self]


/-! ## The residue theorem (`lem:resform`(c)) -/

section ResThm
variable {s : ℕ}

lemma placePoly_monic (a : Fin s → F) (k : Fin s → ℕ) : (placePoly a k).Monic :=
  monic_prod_of_monic _ _ fun c _ => (monic_X_sub_C (a c)).pow (k c)

lemma placePoly_natDegree (a : Fin s → F) (k : Fin s → ℕ) :
    (placePoly a k).natDegree = ∑ c, k c := by
  rw [placePoly, natDegree_prod_of_monic _ _ fun c _ => (monic_X_sub_C (a c)).pow (k c)]
  simp [natDegree_pow]

lemma placeCo_monic (a : Fin s → F) (k : Fin s → ℕ) (c : Fin s) : (placeCo a k c).Monic :=
  monic_prod_of_monic _ _ fun c _ => (monic_X_sub_C (a c)).pow (k c)

lemma placeCo_natDegree (a : Fin s → F) (k : Fin s → ℕ) (c : Fin s) :
    (placeCo a k c).natDegree = ∑ c, k c - k c := by
  rw [placeCo, natDegree_prod_of_monic _ _ fun c _ => (monic_X_sub_C (a c)).pow (k c)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [← Finset.add_sum_erase _ _ (mem_univ c)]
  omega

lemma placePoly_eq (a : Fin s → F) (k : Fin s → ℕ) (c : Fin s) :
    placePoly a k = (X - C (a c)) ^ k c * placeCo a k c :=
  (Finset.mul_prod_erase _ _ (mem_univ c)).symm

lemma placeCo_eval_ne (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (c : Fin s) :
    (placeCo a k c).eval (a c) ≠ 0 := by
  rw [placeCo, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun c' hc' => ?_
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hc') (ha h).symm)

lemma dvd_placeCo (a : Fin s → F) (k : Fin s → ℕ) {c c' : Fin s} (h : c ≠ c') :
    (X - C (a c)) ^ k c ∣ placeCo a k c' :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨h, mem_univ c⟩)

/-- **`lem:resform`(c)** (residue theorem on the projective line): for distinct places `a_c` and every
`F = V / ∏_c (z - a_c)^{k_c}`, `∑_c Res_{a_c}(F dz) = [z^{-1}] F`. -/
theorem res_thm (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (V : F[X]) :
    ∑ c, resAt a k V c = resInf a k V := by
  set M := ∑ c, k c with hM
  set D := placePoly a k with hD
  set r : Fin s → F[X] := fun c => locPart (a c) (k c) V (placeCo a k c) with hr
  set R : F[X] := ∑ c, r c * placeCo a k c with hR
  have hkM : ∀ c, k c ≤ M := fun c => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
  -- each summand has degree `≤ M - 1`, and is `0` when `k_c = 0`
  have hterm : ∀ c, r c * placeCo a k c = 0 ∨
      (1 ≤ k c ∧ (r c * placeCo a k c).coeff (M - 1) = resAt a k V c ∧
        (r c * placeCo a k c).natDegree ≤ M - 1) := by
    intro c
    rcases Nat.eq_zero_or_pos (k c) with h0 | hpos
    · left; simp [hr, h0, locPart_zero]
    · right
      have hd1 := locPart_natDegree (a c) (k c) V (placeCo a k c) hpos
      have hd2 := (placeCo_natDegree a k c).le
      have hMe : M - 1 = (k c - 1) + (M - k c) := by have := hkM c; omega
      refine ⟨hpos, ?_, ?_⟩
      · have hlead : (placeCo a k c).coeff (M - k c) = 1 := by
          have := (placeCo_monic a k c).coeff_natDegree
          rwa [placeCo_natDegree] at this
        rw [hMe, coeff_mul_add_eq_of_natDegree_le hd1 hd2, hlead, mul_one,
          locPart_coeff_top _ _ _ _ hpos]
        rfl
      · exact (natDegree_mul_le).trans (by rw [hMe]; exact Nat.add_le_add hd1 hd2)
  -- `R` is the remainder of `V` modulo `D`
  have hdvd : D ∣ V - R := by
    rw [hD, placePoly]
    refine Finset.prod_dvd_of_coprime ?_ fun c _ => ?_
    · intro c _ c' _ hcc'
      exact ((pairwise_coprime_X_sub_C ha) hcc').pow
    · have hsplit : V - R = (V - r c * placeCo a k c) -
          ∑ c' ∈ univ.erase c, r c' * placeCo a k c' := by
        rw [hR, ← Finset.add_sum_erase _ _ (mem_univ c)]; ring
      rw [hsplit]
      refine dvd_sub (locPart_dvd _ _ _ _ (placeCo_eval_ne a ha k c)) ?_
      exact Finset.dvd_sum fun c' hc' =>
        (dvd_placeCo a k (Finset.ne_of_mem_erase hc').symm).mul_left _
  have hRdeg : R.degree < D.degree := by
    rw [degree_eq_natDegree (placePoly_monic a k).ne_zero, placePoly_natDegree]
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · have : R = 0 := by
        rw [hR]
        refine Finset.sum_eq_zero fun c _ => ?_
        rcases hterm c with h | ⟨h1, -⟩
        · exact h
        · have := hkM c; omega
      rw [this, degree_zero]; exact WithBot.bot_lt_coe _
    · refine lt_of_le_of_lt (degree_le_natDegree) (WithBot.coe_lt_coe.mpr ?_)
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := M - 1) _ _ fun c _ => ?_) (show M - 1 < M by omega)
      rcases hterm c with h | ⟨-, -, h⟩
      · rw [h, natDegree_zero]; exact Nat.zero_le _
      · exact h
  have hmod : V %ₘ D = R := by
    rw [modByMonic_eq_of_dvd_sub (placePoly_monic a k) hdvd,
      (modByMonic_eq_self_iff (placePoly_monic a k)).mpr hRdeg]
  rw [resInf, ← hD, hmod, hR, finsetSum_coeff]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases hterm c with h | ⟨-, h, -⟩
  · rw [h, coeff_zero, resAt]
    by_cases hk : k c = 0
    · simp [locRes, hk]
    · have hr0 : r c = 0 := (mul_eq_zero.mp h).resolve_right (placeCo_monic a k c).ne_zero
      rw [← locPart_coeff_top (a c) (k c) V (placeCo a k c) (Nat.pos_of_ne_zero hk)]
      rw [show locPart (a c) (k c) V (placeCo a k c) = r c from rfl, hr0, coeff_zero]
  · exact h.symm

/-- `lem:resform`(c), first case: if `deg V < M = ∑_c k_c`, then `[z^{-1}] F = [z^{M-1}] V`. -/
theorem res_thm_of_deg (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (V : F[X])
    (hV : V.natDegree < ∑ c, k c) :
    ∑ c, resAt a k V c = V.coeff (∑ c, k c - 1) := by
  rw [res_thm a ha k V, resInf, (modByMonic_eq_self_iff (placePoly_monic a k)).mpr]
  rw [degree_eq_natDegree (placePoly_monic a k).ne_zero, placePoly_natDegree]
  exact lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr hV)

/-- `lem:resform`(c), "in particular": the residues add up to `0` when `deg V ≤ ∑_c k_c - 2`
(`F = O(z^{-2})` at `∞`). -/
theorem res_thm_zero (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (V : F[X])
    (hV : V.natDegree + 2 ≤ ∑ c, k c) :
    ∑ c, resAt a k V c = 0 := by
  rw [res_thm_of_deg a ha k V (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

end ResThm

/-! ## Scrambles as residues (`lem:resform`(a)) -/

section ResForm
variable {s : ℕ}

lemma ps_inv_one : (1 : PowerSeries F)⁻¹ = 1 :=
  ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr (one_mul 1)).symm

/-- A Taylor digit is a residue: `[(z - a)^k] V = Res_a(V (z - a)^{-k-1} dz)` (`sec:prelim`). -/
lemma locRes_one (a : F) (k : ℕ) (V : F[X]) : locRes a (k + 1) V 1 = (taylor a V).coeff k := by
  rw [locRes]
  simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [taylor_one, map_one,
    Polynomial.coe_one, ps_inv_one, mul_one, Polynomial.coeff_coe]

lemma vecPoly_coeff (f : ℕ → F) (m j : ℕ) : (vecPoly f m).coeff j = if j < m then f j else 0 := by
  rw [vecPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

/-- The Taylor coefficients of the index polynomial are the unscrambled frame digits:
`[(z - a)^i] V = ∑_j P_a[i][j] V_j`. -/
lemma taylor_coeff_vecPoly (a : F) (f : ℕ → F) (m i : ℕ) :
    (taylor a (vecPoly f m)).coeff i = ∑ j ∈ range m, pas a i j * f j := by
  rw [vecPoly, map_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, LinearMap.map_smul, coeff_smul, taylor_X_pow, coeff_X_add_C_pow, pas,
    smul_eq_mul]
  ring

/-- **`lem:resform`(a)**: for every scramble `L` of the frame, digit `n` of coordinate `c` of the
point with index digits `f_0, …, f_{m-1}` is `∑_{k ≤ n} L_c[n][k] Res_{a_c}(V (z - a_c)^{-k-1} dz)`, the
residue of the index polynomial `V` against the polar differential
`η_{c,n} = ∑_{k ≤ n} L_c[n][k] (z - a_c)^{-k-1} dz` (residues are linear in the differential). -/
theorem scrGen_res (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : ℕ → F) (m : ℕ) (c : Fin s)
    (n : ℕ) :
    ∑ j ∈ range m, scrGen a L c n j * f j =
      ∑ k ∈ range (n + 1), L c n k * locRes (a c) (k + 1) (vecPoly f m) 1 := by
  simp only [scrGen, locRes_one, taylor_coeff_vecPoly, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `P(a) = l_n`: the polar differential `P(z) (z - a)^{-n-1} dz` has exact pole order `n + 1` iff
`l_n ≠ 0` (for a scramble, `L_c[n][n] ≠ 0`). -/
theorem polarNum_eval (a : F) (l : ℕ → F) (n : ℕ) : (polarNum a l n).eval a = l n := by
  rw [polarNum, eval_finset_sum, Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have : 0 < n - k := by simp at hk; omega
    simp [zero_pow this.ne']
  · intro h; simp at h

/-- **`lem:resform`(a)**, one residue: digit `n` of coordinate `c` is `Res_{a_c}(V η_{c,n})` with the polar
differential `η_{c,n} = P_{c,n}(z) (z - a_c)^{-n-1} dz`, `P_{c,n} = ∑_{k ≤ n} L_c[n][k] (z - a_c)^{n-k}`
(`polarNum`), of exact pole order `n + 1` iff `L_c[n][n] ≠ 0` (`polarNum_eval`). -/
theorem scrGen_res_polar (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : ℕ → F) (m : ℕ) (c : Fin s)
    (n : ℕ) :
    ∑ j ∈ range m, scrGen a L c n j * f j =
      locRes (a c) (n + 1) (vecPoly f m * polarNum (a c) (L c n) n) 1 := by
  rw [scrGen_res, locRes_one, taylor_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hP : (taylor (a c) (polarNum (a c) (L c n) n)).coeff (n - k) = L c n k := by
    rw [polarNum, map_sum, finsetSum_coeff, Finset.sum_eq_single k]
    · rw [← smul_eq_C_mul, LinearMap.map_smul, coeff_smul, taylor_pow, taylor_X_sub_C, coeff_X_pow,
        if_pos rfl, smul_eq_mul, mul_one]
    · intro j hj hjk
      rw [← smul_eq_C_mul, LinearMap.map_smul, coeff_smul, taylor_pow, taylor_X_sub_C, coeff_X_pow,
        if_neg (by simp at hj; omega), smul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hP, locRes_one, mul_comm]

end ResForm

end GeoSeq
