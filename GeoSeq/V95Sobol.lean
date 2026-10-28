/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Gen

@[expose] public section

/-!
# GeoSeq stage V9-5 (part 2): Sobol' sequences (`eq:sobrec`, `lem:sobol`, `cor:sobol`)

* Binary digits: `bitZ_xor`, `bitZ_xorSum`, `bitZ_two_pow_mul`, `bitZ_high`; `sobolDir_lt` (`u_k < 2^k` for all
  `k ≥ 1`, from admissibility and the recurrence).
* `scol_rec` (**`eq:sobrec` in digit form**): for the columns `col_j = (C[n][j])_n` (`j ≥ e`),
  `col_j = ∑_{0<i<e} α_i col_{j-i} + col_{j-e} + 2^{-e} col_{j-e}`; `scol_rec_t`: `∑_{t ≤ e} b_t col_{j-e+t} =
  2^{-e} col_{j-e}` over `𝔽_2`.
* `sobY_mul_b` (`lem:sobol`(a)): `y(b V) = 2^{-e} y(V)` digitwise; `sobY_low` ((b)); `sobol_radInv` (**`lem:sobol`**):
  a Sobol' coordinate with constant term `1` and admissible direction numbers is a `b`-adic radical inverse;
  `sobol_pi_unitri`: its digit map is upper unitriangular. `vdc_radInv`: the van der Corput coordinate (`u ≡ 1`) is
  the `z`-adic radical inverse.
* **`sobol_not_qu`** (**`cor:sobol`**): every Sobol' sequence (any `s ≥ 2`, pairwise coprime polynomials with constant
  term `1`, admissible direction numbers, with or without the van der Corput coordinate) is not quasi-uniform, in
  the natural and in the Gray-code order; `sobol_proj` (projections to `s' ≥ 2` coordinates); `sobol_primitive`
  (distinct irreducible polynomials, e.g. Sobol's primitive ones, are pairwise coprime).
-/

namespace GeoSeq

open Finset Polynomial

section Bits

lemma bitZ_xor (x y j : ℕ) : bitZ (x ^^^ y) j = bitZ x j + bitZ y j := by
  unfold bitZ; rw [Nat.testBit_xor]; cases x.testBit j <;> cases y.testBit j <;> decide

lemma bitZ_xorSum (f : ℕ → ℕ) : ∀ n j, bitZ (xorSum f n) j = ∑ i ∈ range n, bitZ (f i) j
  | 0, j => by simp [xorSum, bitZ]
  | n + 1, j => by rw [xorSum, bitZ_xor, bitZ_xorSum f n j, Finset.sum_range_succ]

lemma bitZ_two_pow_mul (i x j : ℕ) : bitZ (2 ^ i * x) j = if i ≤ j then bitZ x (j - i) else 0 := by
  unfold bitZ; rw [Nat.testBit_two_pow_mul]
  by_cases h : i ≤ j <;> simp [h]

lemma bitZ_high {x k j : ℕ} (hx : x < 2 ^ k) (hj : k ≤ j) : bitZ x j = 0 := by
  unfold bitZ
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj))]; simp

lemma bitZ_zero_ (j : ℕ) : bitZ 0 j = 0 := by simp [bitZ]

lemma bitZ_odd {x : ℕ} (hx : x % 2 = 1) : bitZ x 0 = 1 := by
  unfold bitZ; simp [Nat.testBit_zero, hx]

lemma xorSum_lt (f : ℕ → ℕ) (k : ℕ) : ∀ n, (∀ i < n, f i < 2 ^ k) → xorSum f n < 2 ^ k
  | 0, _ => by simp [xorSum]
  | n + 1, h => by
    rw [xorSum]
    exact Nat.xor_lt_two_pow (xorSum_lt f k n fun i hi => h i (by omega)) (h n (by omega))

lemma ite_bitZ_mul (c : Prop) [Decidable c] (x j : ℕ) :
    bitZ (if c then x else 0) j = if c then bitZ x j else 0 := by
  split_ifs <;> simp [bitZ_zero_]

end Bits

section Dir
variable {b : (ZMod 2)[X]} {u : ℕ → ℕ}

lemma two_pow_mul_lt {i k x : ℕ} (hik : i ≤ k) (hx : x < 2 ^ (k - i)) : 2 ^ i * x < 2 ^ k := by
  calc 2 ^ i * x < 2 ^ i * 2 ^ (k - i) := Nat.mul_lt_mul_of_pos_left hx (by positivity)
    _ = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' hik]

/-- Admissible direction numbers satisfy `u_k < 2^k` for every `k ≥ 1`. -/
theorem sobolDir_lt (hb : 1 ≤ b.natDegree) (h : IsSobolDir b u) : ∀ k, 1 ≤ k → u k < 2 ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hke : k ≤ b.natDegree
    · exact (h.1 k hk hke).2
    · push Not at hke
      rw [h.2 k hke]
      have he : u (k - b.natDegree) < 2 ^ (k - b.natDegree) := ih _ (by omega) (by omega)
      refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ (two_pow_mul_lt (by omega) he))
        (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega)))
      refine xorSum_lt _ _ _ fun i hi => ?_
      split_ifs
      · exact two_pow_mul_lt (by omega) (ih _ (by omega) (by omega))
      · exact Nat.two_pow_pos k

lemma sobolGen_eq {s : ℕ} (u : Fin s → ℕ → ℕ) (c : Fin s) : sobolGen u c = scol (u c) := rfl

/-- **`eq:sobrec` in digit form**: for `j ≥ e`, column `j` is `∑_{0<i<e} α_i col_{j-i} + col_{j-e} + 2^{-e} col_{j-e}`
(the last term shifted down by `e` digits). -/
theorem scol_rec (hb : 1 ≤ b.natDegree) (h : IsSobolDir b u) (j : ℕ) (hj : b.natDegree ≤ j) (n : ℕ) :
    scol u n j = (∑ i ∈ range b.natDegree,
        if i ≠ 0 ∧ b.coeff (b.natDegree - i) = 1 then scol u n (j - i) else 0) +
      scol u n (j - b.natDegree) +
      (if b.natDegree ≤ n then scol u (n - b.natDegree) (j - b.natDegree) else 0) := by
  set e := b.natDegree with he
  have hlt := sobolDir_lt hb h
  by_cases hn : n ≤ j
  · rw [scol, if_pos hn, h.2 (j + 1) (by omega), bitZ_xor, bitZ_xor, bitZ_xorSum]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [ite_bitZ_mul]
      split_ifs with hc
      · rw [bitZ_two_pow_mul, scol]
        by_cases hin : i ≤ j - n
        · rw [if_pos hin, if_pos (by omega), show j + 1 - i = j - i + 1 by omega,
            show j - n - i = j - i - n by omega]
        · rw [if_neg hin, if_neg (by omega)]
      · rfl
    · rw [bitZ_two_pow_mul, scol]
      by_cases hen : e ≤ j - n
      · rw [if_pos hen, if_pos (by omega), show j + 1 - e = j - e + 1 by omega,
          show j - n - e = j - e - n by omega]
      · rw [if_neg hen, if_neg (by omega)]
    · by_cases hen : e ≤ n
      · rw [if_pos hen, scol, if_pos (by omega), show j + 1 - e = j - e + 1 by omega,
          show j - e - (n - e) = j - n by omega]
      · rw [if_neg hen]
        exact bitZ_high (hlt (j + 1 - e) (by omega)) (by omega)
  · rw [scol, if_neg hn]
    have h1 : ∀ i, scol u n (j - i) = 0 := fun i => by rw [scol, if_neg (by omega)]
    rw [Finset.sum_eq_zero fun i _ => by split_ifs <;> first | rfl | exact h1 _, h1, zero_add, zero_add]
    split_ifs with hen
    · rw [scol, if_neg (by omega)]
    · rfl

lemma zmod2_ite (a x : ZMod 2) : (if a = 1 then x else 0) = a * x := by
  revert a x; decide

lemma zmod2_lead (f : (ZMod 2)[X]) (hf : f ≠ 0) : f.coeff f.natDegree = 1 := by
  have h := leadingCoeff_ne_zero.mpr hf
  unfold leadingCoeff at h
  revert h; generalize f.coeff f.natDegree = x; revert x; decide

/-- `eq:sobrec` over `𝔽_2` in the form `∑_{t ≤ e} b_t col_{j-e+t} = 2^{-e} col_{j-e}` (`b_0 = b_e = 1`). -/
theorem scol_rec_t (hb : 1 ≤ b.natDegree) (hb0 : b.coeff 0 = 1) (h : IsSobolDir b u) (j : ℕ)
    (hj : b.natDegree ≤ j) (n : ℕ) :
    ∑ t ∈ range (b.natDegree + 1), b.coeff t * scol u n (j - b.natDegree + t) =
      if b.natDegree ≤ n then scol u (n - b.natDegree) (j - b.natDegree) else 0 := by
  have hbne : b ≠ 0 := by rintro rfl; simp at hb
  set e := b.natDegree with he
  have hlead : b.coeff e = 1 := zmod2_lead b hbne
  have hrec := scol_rec hb h j hj n
  rw [Finset.sum_range_succ, hlead, one_mul, show j - e + e = j by omega, hrec]
  have hS : (∑ i ∈ range e, if i ≠ 0 ∧ b.coeff (e - i) = 1 then scol u n (j - i) else 0) =
      ∑ t ∈ Finset.Ico 1 e, b.coeff t * scol u n (j - e + t) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), if_neg (by simp), zero_add]
    refine Finset.sum_nbij' (fun i => e - i) (fun t => e - t) (fun i hi => ?_) (fun t ht => ?_)
      (fun i hi => ?_) (fun t ht => ?_) (fun i hi => ?_)
    · simp only [Finset.mem_Ico] at hi ⊢; omega
    · simp only [Finset.mem_Ico] at ht ⊢; omega
    · simp only [Finset.mem_Ico] at hi; omega
    · simp only [Finset.mem_Ico] at ht; omega
    · simp only [Finset.mem_Ico] at hi
      have hi0 : ¬ i = 0 := by omega
      simp only [ne_eq, hi0, not_false_eq_true, true_and]
      rw [zmod2_ite, show j - e + (e - i) = j - i by omega]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [hS, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < e), hb0, one_mul, add_zero]
  linear_combination (∑ t ∈ Finset.Ico 1 e, b.coeff t * scol u n (j - e + t) + scol u n (j - e)) * h2

end Dir

section Coord

lemma sobY_eq_genY {s : ℕ} (u : Fin s → ℕ → ℕ) (c : Fin s) : genY (sobolGen u) c = sobY (u c) := rfl

lemma sobY_lin (u : ℕ → ℕ) : IsLinCoord (sobY u) := genY_lin (sobolGen fun _ : Fin 1 => u) 0

lemma sobY_add (u : ℕ → ℕ) (V W : (ZMod 2)[X]) (n : ℕ) : sobY u (V + W) n = sobY u V n + sobY u W n :=
  sobY_lin u V W n

lemma sobY_range (u : ℕ → ℕ) (V : (ZMod 2)[X]) (n N : ℕ) (hN : V.natDegree < N) :
    sobY u V n = ∑ m ∈ range N, scol u n m * V.coeff m :=
  Polynomial.sum_over_range' _ (fun _ => mul_zero _) N hN

lemma sobY_C_mul (u : ℕ → ℕ) (r : ZMod 2) (V : (ZMod 2)[X]) (n : ℕ) :
    sobY u (C r * V) n = r * sobY u V n := by
  rw [sobY_range u _ n (V.natDegree + 1) (lt_of_le_of_lt (natDegree_C_mul_le r V) (by omega)),
    sobY_range u V n (V.natDegree + 1) (by omega), Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [coeff_C_mul]; ring

variable {b : (ZMod 2)[X]} {u : ℕ → ℕ}

lemma sobY_b_X_pow (hb : 1 ≤ b.natDegree) (k n : ℕ) :
    sobY u (b * X ^ k) n = ∑ t ∈ range (b.natDegree + 1), b.coeff t * scol u n (k + t) := by
  have hdeg : (b * X ^ k).natDegree < k + (b.natDegree + 1) := by
    have := natDegree_mul_le (p := b) (q := X ^ k); rw [natDegree_X_pow] at this; omega
  rw [sobY_range u _ n _ hdeg, Finset.sum_range_add, Finset.sum_eq_zero fun m hm => ?_, zero_add]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [coeff_mul_X_pow', if_pos (by omega), show k + t - k = t by omega]; ring
  · rw [coeff_mul_X_pow', if_neg (by have := Finset.mem_range.mp hm; omega), mul_zero]

/-- **`lem:sobol`(a)**: multiplication by `b` shifts the digits by `e` places, `y(b V) = 2^{-e} y(V)`. -/
theorem sobY_mul_b (hb : 1 ≤ b.natDegree) (hb0 : b.coeff 0 = 1) (h : IsSobolDir b u) (V : (ZMod 2)[X])
    (n : ℕ) : sobY u (b * V) n = if b.natDegree ≤ n then sobY u V (n - b.natDegree) else 0 := by
  induction V using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [mul_add, sobY_add, hP, hQ, sobY_add]
    split_ifs <;> simp
  | monomial k r =>
    rw [← C_mul_X_pow_eq_monomial, show b * (C r * X ^ k) = C r * (b * X ^ k) by ring, sobY_C_mul,
      sobY_b_X_pow hb, sobY_C_mul]
    have hrec := scol_rec_t hb hb0 h (k + b.natDegree) (by omega) n
    rw [show k + b.natDegree - b.natDegree = k by omega] at hrec
    rw [hrec]
    split_ifs
    · rw [sobY_range u _ _ (k + 1) (by rw [natDegree_X_pow]; omega), Finset.sum_range_succ,
        Finset.sum_eq_zero fun m hm => by
          rw [coeff_X_pow, if_neg (by have := Finset.mem_range.mp hm; omega), mul_zero],
        coeff_X_pow, if_pos rfl, zero_add, mul_one]
    · rw [mul_zero]

/-- **`lem:sobol`(b)**: for `deg a < e` the point `y(a)` has no digits beyond position `e - 1`. -/
theorem sobY_low (a : (ZMod 2)[X]) (e : ℕ) (ha : a.natDegree < e) (n : ℕ) (hn : e ≤ n) :
    sobY u a n = 0 := by
  rw [sobY_range u a n e ha]
  exact Finset.sum_eq_zero fun m hm => by
    rw [scol, if_neg (by have := Finset.mem_range.mp hm; omega), zero_mul]

/-- The digit map of `lem:sobol` is upper unitriangular: `π(z^j)_i = 0` for `i > j` and `π(z^j)_j = 1` (`j < e`). -/
theorem sobol_pi_unitri (hb : 1 ≤ b.natDegree) (h : IsSobolDir b u) (j i : ℕ) (hj : j < b.natDegree) :
    sobY u (X ^ j) i = if j < i then 0 else if i = j then 1 else sobY u (X ^ j) i := by
  rw [sobY_range u _ i (j + 1) (by rw [natDegree_X_pow]; omega), Finset.sum_range_succ,
    Finset.sum_eq_zero fun m hm => by
      rw [coeff_X_pow, if_neg (by have := Finset.mem_range.mp hm; omega), mul_zero],
    coeff_X_pow, if_pos rfl, zero_add, mul_one, scol]
  split_ifs <;> first | omega | rfl |
    (rw [show j - i = 0 by omega]; exact bitZ_odd (h.1 (j + 1) (by omega) (by omega)).1)

lemma vecPolyF_coeff (e : ℕ) (v : Fin e → ZMod 2) (m : ℕ) :
    (∑ j : Fin e, C (v j) * X ^ (j : ℕ)).coeff m = if h : m < e then v ⟨m, h⟩ else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with hm
  · rw [Finset.sum_eq_single ⟨m, hm⟩ (fun x _ hx => if_neg fun h' => hx (Fin.ext h'.symm)) (by simp),
      if_pos rfl]
  · exact Finset.sum_eq_zero fun x _ => if_neg fun (h' : m = (x : ℕ)) => hm (h' ▸ x.isLt)

lemma vecPolyF_natDegree (e : ℕ) (he : 1 ≤ e) (v : Fin e → ZMod 2) :
    (∑ j : Fin e, C (v j) * X ^ (j : ℕ)).natDegree < e := by
  rw [Nat.lt_iff_le_pred he]
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := j.isLt; omega

/-- **`lem:sobol`**: a Sobol' coordinate whose polynomial `b` (degree `e ≥ 1`) has constant term `1`, with admissible
direction numbers, is a `b`-adic radical inverse; the digit map is `π(a)_i = y(a)_i` (upper unitriangular,
`sobol_pi_unitri`). Primitivity is not used. -/
theorem sobol_radInv (hb : 1 ≤ b.natDegree) (hb0 : b.coeff 0 = 1) (h : IsSobolDir b u) :
    IsRadInv (sobY u) b (sobY u) := by
  set e := b.natDegree with he
  have hdec : ∀ V : (ZMod 2)[X], ∃ a W : (ZMod 2)[X], a.natDegree < e ∧ V = a + b * W := fun V =>
    ⟨V % b, V / b, natDegree_mod_lt V (by omega), (EuclideanDomain.mod_add_div V b).symm⟩
  refine ⟨fun w => ?_, fun V Q i hi => ?_⟩
  · -- onto, by injectivity of the triangular map on `𝔽_2^e`
    let Φ : (Fin e → ZMod 2) → (Fin e → ZMod 2) := fun v i => sobY u (∑ j : Fin e, C (v j) * X ^ (j : ℕ)) i
    have hinj : Function.Injective Φ := by
      intro v v' hvv
      by_contra hne
      set P : (ZMod 2)[X] := ∑ j : Fin e, C (v j) * X ^ (j : ℕ) - ∑ j : Fin e, C (v' j) * X ^ (j : ℕ)
      have hP0 : P ≠ 0 := by
        intro h0
        apply hne
        funext j
        have := congrArg (fun f => f.coeff j) h0
        simp only [P, coeff_sub, vecPolyF_coeff, dif_pos j.isLt, coeff_zero] at this
        exact sub_eq_zero.mp this
      set J := P.natDegree
      have hJ : J < e := lt_of_le_of_lt (natDegree_sub_le _ _)
        (max_lt (vecPolyF_natDegree e hb v) (vecPolyF_natDegree e hb v'))
      have hval : sobY u P J = P.coeff J := by
        rw [sobY_range u P J (J + 1) (by omega), Finset.sum_range_succ,
          Finset.sum_eq_zero fun m hm => by
            rw [scol, if_neg (by have := Finset.mem_range.mp hm; omega), zero_mul], zero_add, scol,
          if_pos le_rfl, Nat.sub_self, bitZ_odd (h.1 (J + 1) (by omega) (by omega)).1, one_mul]
      have hzero : sobY u P J = 0 := by
        have h1 := sobY_add u P (∑ j : Fin e, C (v' j) * X ^ (j : ℕ)) J
        rw [show P + ∑ j : Fin e, C (v' j) * X ^ (j : ℕ) = ∑ j : Fin e, C (v j) * X ^ (j : ℕ) by
          simp [P]] at h1
        have h2 := congrFun hvv ⟨J, hJ⟩
        simp only [Φ] at h2
        rw [h2] at h1
        linear_combination -h1
      exact (leadingCoeff_ne_zero.mpr hP0) (by rw [leadingCoeff, ← hval, hzero])
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj (fun i => w i)
    refine ⟨∑ j : Fin e, C (v j) * X ^ (j : ℕ), vecPolyF_natDegree e hb v, fun i hi => ?_⟩
    exact congrFun hv ⟨i, hi⟩
  · -- digit block `Q` is `π(a_Q)`, by induction on `Q`
    induction Q generalizing V with
    | zero =>
      obtain ⟨a, W, ha, rfl⟩ := hdec V
      rw [zero_mul, zero_add, badicDigit_base ha, sobY_add, sobY_mul_b hb hb0 h, if_neg (by omega), add_zero]
    | succ Q ih =>
      obtain ⟨a, W, ha, rfl⟩ := hdec V
      rw [badicDigit_succ ha, sobY_add, sobY_low a e ha _ (by nlinarith), zero_add, sobY_mul_b hb hb0 h,
        if_pos (by nlinarith), show (Q + 1) * e + i - e = Q * e + i by rw [add_mul, one_mul]; omega]
      exact ih W

/-- The van der Corput coordinate (`C = I`, direction numbers `u_k = 1`) is the `z`-adic radical inverse with digit
map `a ↦ [z^0] a`. -/
theorem vdc_radInv (u : ℕ → ℕ) (hu : ∀ k, 1 ≤ k → u k = 1) :
    IsRadInv (sobY u) X (fun a _ => a.coeff 0) := by
  have hY : sobY u = fun V n => (1 : ZMod 2) * 1 ^ n * (taylor (0 : ZMod 2) V).coeff n := by
    funext V n
    rw [taylor_zero, one_pow, one_mul, one_mul,
      sobY_range u V n (max (n + 1) (V.natDegree + 1)) (by omega)]
    rw [Finset.sum_eq_single n]
    · rw [scol, if_pos le_rfl, Nat.sub_self, hu (n + 1) (by omega), bitZ_odd (by norm_num), one_mul]
    · intro m _ hmn
      rw [scol]
      split_ifs with hm
      · rw [hu (m + 1) (by omega), bitZ_high (k := 1) (by norm_num) (by omega), zero_mul]
      · rw [zero_mul]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  have h := scaledFrame_isRadInv (0 : ZMod 2) 1 1 one_ne_zero one_ne_zero
  rw [inv_one, map_one, one_mul, map_zero, sub_zero] at h
  rw [hY]
  simpa using h

end Coord

section Main
variable {s : ℕ}

lemma sobolCoord_radInv {b : (ZMod 2)[X]} {u : ℕ → ℕ} (h : SobolCoord b u) :
    1 ≤ b.natDegree ∧ ∃ π, IsRadInv (sobY u) b π := by
  rcases h with ⟨rfl, hu⟩ | ⟨hb, hb0, hd⟩
  · exact ⟨by rw [natDegree_X], _, vdc_radInv u hu⟩
  · exact ⟨hb, _, sobol_radInv hb hb0 hd⟩

/-- **`cor:sobol`**: every Sobol' sequence is not quasi-uniform — in every dimension `s ≥ 2`, for all admissible
direction numbers, for any pairwise coprime polynomials with constant term `1` (with or without the van der
Corput coordinate), in the natural order and in the Gray-code order; and there are close pairs:
for every `ε > 0` some prefix `P_m` has two points closer than `ε 2^{-m/s}`. -/
theorem sobol_not_qu (hs : 2 ≤ s) (b : Fin s → (ZMod 2)[X]) (u : Fin s → ℕ → ℕ)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (hco : ∀ c, SobolCoord (b c) (u c)) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < 2 ^ m ∧ w < 2 ^ m ∧ v ≠ w ∧
        euclDist (seqPoint (zcode 2) (sobolGen u) v) (seqPoint (zcode 2) (sobolGen u) w) <
          ε * ((2 : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (seqPoint (zcode 2) (sobolGen u)) ∧
      ¬ IsQuasiUniform (seqPoint (zcode 2) (sobolGen u) ∘ gray) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := fun c => (sobolCoord_radInv (hco c)).1
  have ch : Fin s := ⟨0, by omega⟩
  obtain ⟨π, hπ⟩ := (sobolCoord_radInv (hco ch)).2
  have key := nonqu hs (fun c => sobY (u c)) (fun c => sobY_lin (u c)) b hdeg hcop ch
    (fun c _ => by
      obtain ⟨π', hπ'⟩ := (sobolCoord_radInv (hco c)).2
      exact hπ'.isBAdic (hdeg c) (sobY_lin (u c))) π hπ
  have he : seqPoint (zcode 2) (sobolGen u) = linPt 2 (fun c => sobY (u c)) := by
    rw [seqPoint_eq_linPt]; rfl
  rw [he]
  refine ⟨key.1, key.2, not_qu_comp le_rfl (by omega) _ (fun v c => linPt_mem _ v c) gray
    (fun m v hv => gray_surj m v hv) key.1⟩

/-- **`cor:sobol`**, projections: the projection of a Sobol' sequence to any `s' ≥ 2` of its coordinates
(`ι : Fin s' → Fin s` injective) is not quasi-uniform. -/
theorem sobol_proj {s' : ℕ} (hs' : 2 ≤ s') (b : Fin s → (ZMod 2)[X]) (u : Fin s → ℕ → ℕ)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (hco : ∀ c, SobolCoord (b c) (u c))
    (ι : Fin s' → Fin s) (hι : Function.Injective ι) :
    ¬ IsQuasiUniform (fun v (c' : Fin s') => seqPoint (zcode 2) (sobolGen u) v (ι c')) :=
  (sobol_not_qu hs' (b ∘ ι) (u ∘ ι) (fun c c' h => hcop (hι.ne h)) (fun c => hco (ι c))).2.1

/-- Distinct irreducible polynomials over `𝔽_2` (e.g. Sobol's primitive polynomials) are pairwise coprime. -/
theorem sobol_primitive (b : Fin s → (ZMod 2)[X]) (hirr : ∀ c, Irreducible (b c))
    (hinj : Function.Injective b) : Pairwise fun c c' => IsCoprime (b c) (b c') := by
  intro c c' hcc
  have hmonic : ∀ c, (b c).Monic := fun c => by
    have := zmod2_lead (b c) (hirr c).ne_zero
    exact this
  refine (Irreducible.coprime_iff_not_dvd (hirr c)).mpr fun hd => hinj.ne hcc ?_
  exact eq_of_monic_of_associated (hmonic c) (hmonic c') (Irreducible.associated_of_dvd (hirr c) (hirr c') hd)

end Main

end GeoSeq
