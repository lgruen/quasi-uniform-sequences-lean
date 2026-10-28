/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.WFLaw
public import GeoSeq.Series
public import GeoSeq.B3Defs

@[expose] public section

/-!
# GeoSeq stage S6: the Kummer root over `𝔽_3` and Cartier operators (`lem:frames`, `sec:automata`)

* Polynomials as lists (`lps L = ∑ L_n x^n`) with computable sum, product, Cartier selection
  (`ev3 r L` = every third coefficient from `r`) and trimming, and their `PowerSeries` meaning.
* `lem:frames`(b) for `q = 3`: `T3 = τ^{-1}` (`tau3 * T3 = 1`), the Mahler equation
  `T3(x) = (1 + x) T3(x³)` and the digit rule of its coefficients (`B3_frames`).
* The Cartier operators `Λ_r` (`lam3`) and the identity `[x^{3m+r}] N(x) A(x³) = [x^m] Λ_r(N) A`.
* The states of `prop:automaton` in the Kummer case (`ϑ = τ^{-1}`, `A = 1 + x`, `B = 0`):
  a pair of numerator polynomials `(P_0, P_1)` stands for the Laurent series
  `x^{-8} (P_0 + P_1 τ^{-1}) / Q_p`, `Q_p = 2 + x²`; its coefficient `n` is
  `[x^{n+8}] (P_0 + P_1 T3) Q_p^{-1}` (`esem`). One Cartier step on numerators (`stepP`) is the
  transition of the automaton (`cartier_step`), and the readout `[x^0]` is computable (`acoef`).
* Reachability: a finite list of state vectors closed under the steps (a certificate checked by
  `decide`) contains a state for every digit word (`reach_A`, `reach_B`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Polynomials as lists -/

section Lists

variable {R : Type*} [CommRing R]

lemma lget_nil' (n : ℕ) : lget ([] : List R) n = 0 := by simp [lget]

lemma lget_cons0 (x : R) (L : List R) : lget (x :: L) 0 = x := by simp [lget]

lemma lget_cons_succ (x : R) (L : List R) (n : ℕ) : lget (x :: L) (n + 1) = lget L n := by
  simp [lget]

lemma lps_nil : lps ([] : List R) = 0 := by
  ext n; simp [lps, lget_nil']

lemma lps_cons (x : R) (L : List R) : lps (x :: L) = C x + X * lps L := by
  ext n
  rcases n with _ | n
  · simp [lps, lget_cons0]
  · rw [map_add, coeff_succ_X_mul]
    simp [lps, lget_cons_succ, coeff_C]

lemma lget_padd (a b : List R) (n : ℕ) : lget (padd a b) n = lget a n + lget b n := by
  induction a generalizing b n with
  | nil => simp [padd, lget_nil']
  | cons x a ih =>
    cases b with
    | nil => simp [padd, lget_nil']
    | cons y b =>
      rcases n with _ | n
      · simp [padd, lget_cons0]
      · simp only [padd, lget_cons_succ]; exact ih b n

lemma lps_padd (a b : List R) : lps (padd a b) = lps a + lps b := by
  ext n; simp [lps, lget_padd]

lemma lps_map_mul (c : R) (L : List R) : lps (L.map (c * ·)) = C c * lps L := by
  ext n
  simp only [lps, coeff_mk, coeff_C_mul, lget]
  rcases Nat.lt_or_ge n L.length with h | h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma lps_pmul (a b : List R) : lps (pmul a b) = lps a * lps b := by
  induction a with
  | nil => simp [pmul, lps_nil]
  | cons x a ih =>
    rw [pmul, lps_padd, lps_map_mul, lps_cons, lps_cons, ih, map_zero]
    ring

lemma lps_pneg (L : List R) : lps (pneg L) = -lps L := by
  have : pneg L = L.map ((-1 : R) * ·) := by
    unfold pneg; congr 1; funext y; ring
  rw [this, lps_map_mul]; simp

lemma lps_pshift (k : ℕ) (L : List R) : lps (pshift k L) = X ^ k * lps L := by
  induction k with
  | zero => simp [pshift]
  | succ k ih =>
    have : pshift (k + 1) L = 0 :: pshift k L := by simp [pshift, List.replicate_succ]
    rw [this, lps_cons, ih, map_zero]; ring

lemma lget_ev3 (k : ℕ) (L : List R) (n : ℕ) : lget (ev3 k L) n = lget L (k + 3 * n) := by
  induction L generalizing k n with
  | nil => simp [ev3, lget_nil']
  | cons x r ih =>
    rcases k with _ | k
    · rcases n with _ | n
      · simp [ev3, lget_cons0]
      · simp only [ev3, lget_cons_succ]
        rw [ih 2 n, show 0 + 3 * (n + 1) = (2 + 3 * n) + 1 by ring, lget_cons_succ]
    · simp only [ev3]
      rw [ih k n, show k + 1 + 3 * n = (k + 3 * n) + 1 by ring, lget_cons_succ]

lemma lget_trim [DecidableEq R] (L : List R) (n : ℕ) : lget (trim L) n = lget L n := by
  induction L generalizing n with
  | nil => simp [trim]
  | cons x xs ih =>
    unfold trim
    by_cases h : trim xs = [] ∧ x = 0
    · rw [ite_cond_eq_true _ _ (eq_true h), lget_nil']
      rcases n with _ | n
      · rw [lget_cons0, h.2]
      · rw [lget_cons_succ, ← ih n, h.1, lget_nil']
    · rw [ite_cond_eq_false _ _ (eq_false h)]
      rcases n with _ | n
      · simp [lget_cons0]
      · rw [lget_cons_succ, lget_cons_succ, ih n]

lemma lps_trim [DecidableEq R] (L : List R) : lps (trim L) = lps L := by
  ext n; simp [lps, lget_trim]

lemma lps_ev3 (r : ℕ) (L : List R) : lps (ev3 r L) = lam3 r (lps L) := by
  ext n; simp [lps, lam3, lget_ev3, add_comm]

end Lists


/-! ## Base three: `τ`, the Kummer root `T3 = τ^{-1}` and its Mahler equation (`lem:frames`(b)) -/

lemma ps3_three : (3 : PowerSeries (ZMod 3)) = 0 := by
  rw [show (3 : PowerSeries (ZMod 3)) = C (3 : ZMod 3) from (map_ofNat C 3).symm]
  rw [show (3 : ZMod 3) = 0 from rfl, map_zero]

/-- Frobenius over `𝔽_3`: `F(x³) = F(x)³`. -/
lemma frob3 (F : PowerSeries (ZMod 3)) : expand 3 three_ne_zero F = F ^ 3 := by
  convert FiniteField.PowerSeries.expand_card F <;> exact (ZMod.card 3).symm

lemma t3cAux_congr : ∀ (f f' n : ℕ), n ≤ f → n ≤ f' → t3cAux f n = t3cAux f' n := by
  intro f
  induction f with
  | zero =>
    intro f' n hn _
    obtain rfl : n = 0 := by omega
    cases f' <;> simp [t3cAux]
  | succ f ih =>
    intro f' n hn hn'
    rcases f' with _ | f'
    · obtain rfl : n = 0 := by omega
      simp [t3cAux]
    · simp only [t3cAux]
      by_cases h0 : n = 0
      · simp [h0]
      · rw [ih f' (n / 3) (by omega) (by omega)]

/-- The digit recursion of `t3c`. -/
lemma t3c_rec (n : ℕ) :
    t3c n = if n = 0 then 1 else if n % 3 = 2 then 0 else t3c (n / 3) := by
  rcases n with _ | m
  · simp [t3c, t3cAux]
  · unfold t3c
    simp only [t3cAux, Nat.add_one_ne_zero, ite_false]
    rw [t3cAux_congr m ((m + 1) / 3) _ (by omega) le_rfl]

/-- **`lem:frames`(b)**, Mahler equation: `T3(x) = (1 + x) T3(x³)`. -/
lemma T3_mahler : T3 = (1 + X) * expand 3 three_ne_zero T3 := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_expand]
  rcases n with _ | m
  · simp [T3, t3c, t3cAux]
  · rw [coeff_succ_X_mul, coeff_expand]
    simp only [T3, coeff_mk]
    rw [t3c_rec (m + 1)]
    simp only [Nat.add_one_ne_zero, ite_false]
    have h3 : (m + 1) % 3 = 0 ∨ (m + 1) % 3 = 1 ∨ (m + 1) % 3 = 2 := by omega
    rcases h3 with h | h | h
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), add_zero]
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), zero_add]
      congr 1; omega
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), add_zero]

lemma T3_const : constantCoeff T3 = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [T3, t3c, t3cAux]

lemma T3_sq : (1 + X) * T3 ^ 2 = 1 := by
  have hm := T3_mahler
  rw [frob3] at hm
  have hne : T3 ≠ 0 := fun h => by
    have := T3_const; rw [h, map_zero] at this; exact zero_ne_one this
  have h : T3 * ((1 + X) * T3 ^ 2 - 1) = 0 := by linear_combination -hm
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

lemma tau3_sq : tau3 ^ 2 = 1 + X := by
  have h := rhoWF_sq 3 le_rfl 1
  simpa [tau3] using h

lemma tau3_const : constantCoeff tau3 = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [tau3, rhoWF, coeff_mk, sqrtCoeff]

/-- **`lem:frames`(b)**: `T3 = τ^{-1}`. -/
lemma tau3_T3 : tau3 * T3 = 1 := by
  set u := tau3 * T3 with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, mul_pow, tau3_sq]; exact T3_sq
  have hc : constantCoeff u = 1 := by rw [hu, map_mul, tau3_const, T3_const, one_mul]
  have hne : u + 1 ≠ 0 := fun h => by
    have := congrArg constantCoeff h
    rw [map_add, hc, map_one, map_zero] at this
    exact absurd this (by decide)
  have h : (u - 1) * (u + 1) = 0 := by linear_combination hu2
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

lemma tau3_eq : tau3 = (1 + X) * T3 := by
  have h1 := tau3_T3
  have h2 := tau3_sq
  linear_combination T3 * h2 - tau3 * h1

lemma tau3_inv : tau3⁻¹ = T3 := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by rw [tau3_const]; exact one_ne_zero)]
  rw [mul_comm]; exact tau3_T3

/-- The digit rule of `lem:frames`(b): `[x^n] τ^{-1} = 1` iff every base-3 digit of `n` is `0` or `1`. -/
lemma t3c_digits (n : ℕ) : t3c n = if ∀ d ∈ Nat.digits 3 n, d ≤ 1 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [t3c, t3cAux]
    · rw [t3c_rec, if_neg (by omega), Nat.digits_def' (by norm_num) hn]
      by_cases h2 : n % 3 = 2
      · rw [if_pos h2, if_neg]; intro h; have := h (n % 3) (by simp); omega
      · rw [if_neg h2, ih (n / 3) (by omega)]
        have hle : n % 3 ≤ 1 := by omega
        by_cases hall : ∀ d ∈ Nat.digits 3 (n / 3), d ≤ 1
        · rw [if_pos hall, if_pos]
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hle
          · exact hall d hd
        · rw [if_neg hall, if_neg]
          intro h; exact hall fun d hd => h d (List.mem_cons_of_mem _ hd)

/-- **`lem:frames`(b) for `q = 3`**: the Kummer root `T3 = ∏_{i≥0}(1 + x^{3^i})` is `τ^{-1}`
(`τ = √(1+x)`), it satisfies the Mahler equation `T3(x) = (1 + x) T3(x³)`, and `[x^n] T3 = 1` exactly
when every base-3 digit of `n` is `0` or `1` (`0` otherwise). -/
theorem B3_frames : tau3 * T3 = 1 ∧ T3 = (1 + X) * expand 3 three_ne_zero T3 ∧
    ∀ n, coeff n T3 = if ∀ d ∈ Nat.digits 3 n, d ≤ 1 then 1 else 0 :=
  ⟨tau3_T3, T3_mahler, fun n => by rw [T3, coeff_mk, t3c_digits]⟩

/-! ## The Cartier operators and the identity `[x^{3m+r}] N(x) A(x³) = [x^m] Λ_r(N) A` -/

section Cartier

variable {R : Type*} [CommRing R]

lemma coeff_Xpow_expand (r n : ℕ) (F : PowerSeries R) :
    coeff n (X ^ r * expand 3 three_ne_zero F) =
      if r ≤ n ∧ 3 ∣ (n - r) then coeff ((n - r) / 3) F else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : r ≤ n
  · simp [h]
  · simp [h]

lemma decomp3 (N : PowerSeries R) :
    N = ∑ r ∈ range 3, X ^ r * expand 3 three_ne_zero (lam3 r N) := by
  ext n
  rw [map_sum, Finset.sum_eq_single (n % 3)]
  · rw [coeff_Xpow_expand, if_pos ⟨Nat.mod_le n 3, Nat.dvd_sub_mod n⟩, lam3, coeff_mk]
    rw [show 3 * ((n - n % 3) / 3) + n % 3 = n by omega]
  · intro r hr hne
    rw [coeff_Xpow_expand, if_neg]
    rintro ⟨h1, d, hd⟩
    have := Finset.mem_range.mp hr
    omega
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.mod_lt n (by norm_num))) h

lemma coeff_mul_expand (N A : PowerSeries R) (m r : ℕ) (hr : r < 3) :
    coeff (3 * m + r) (N * expand 3 three_ne_zero A) = coeff m (lam3 r N * A) := by
  conv_lhs => rw [decomp3 N]
  have e : ∀ r', X ^ r' * expand 3 three_ne_zero (lam3 r' N) * expand 3 three_ne_zero A =
      X ^ r' * expand 3 three_ne_zero (lam3 r' N * A) := fun r' => by rw [map_mul]; ring
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single r]
  · rw [e, coeff_Xpow_expand, if_pos ⟨by omega, ⟨m, by omega⟩⟩]
    rw [show (3 * m + r - r) / 3 = m by omega]
  · intro r' hr' hne
    rw [e, coeff_Xpow_expand, if_neg]
    rintro ⟨h1, d, hd⟩
    have := Finset.mem_range.mp hr'
    omega
  · intro h; exact absurd (Finset.mem_range.mpr hr) h

end Cartier

/-! ## States of the automaton (`prop:automaton`, Kummer case, `q = 3`) -/

lemma Qp3_const : constantCoeff (lps Qp3) = 2 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [lps, Qp3, lget]

lemma Qp3_unit : lps Qp3 * (lps Qp3)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [Qp3_const]; decide)

lemma lps_W3 : lps W3 = X ^ 16 * (lps Qp3 * lps Qp3) := by
  have e : W3 = pshift 16 (pmul Qp3 Qp3) := by decide
  rw [e, lps_pshift, lps_pmul]

lemma lps_Wx3 : lps Wx3 = lps W3 * (1 + X) := by
  have e : Wx3 = pmul W3 [1, 1] := by decide
  rw [e, lps_pmul]
  congr 1
  rw [lps_cons, lps_cons, lps_nil]; simp

/-- **The Cartier step** (`prop:automaton`, proof): for `r < 3`, coefficient `3n + r` of a state is
coefficient `n` of `stepP r` of it. -/
theorem cartier_step (S : St3) (n r : ℕ) (hr : r < 3) :
    coeff (3 * n + r + 8) (esem S) = coeff (n + 8) (esem (stepP r S)) := by
  set Q := lps Qp3
  set Qi := Q⁻¹
  have hQ : Q * Qi = 1 := Qp3_unit
  have hQi : Qi = Q ^ 2 * expand 3 three_ne_zero Qi := by
    rw [frob3]; linear_combination (Qi * (1 + Q * Qi)) * hQ.symm
  have hT := T3_mahler
  have hX : X ^ 16 * esem S = lps (pmul S.1 W3) * expand 3 three_ne_zero Qi +
      lps (pmul S.2 Wx3) * expand 3 three_ne_zero (T3 * Qi) := by
    rw [lps_pmul, lps_pmul, lps_Wx3, lps_W3, map_mul, esem]
    linear_combination (X ^ 16 * lps S.2 * Qi) * hT +
      (X ^ 16 * (lps S.1 + lps S.2 * (1 + X) * expand 3 three_ne_zero T3)) * hQi
  have h1 : coeff (3 * n + r + 8) (esem S) = coeff (3 * (n + 8) + r) (X ^ 16 * esem S) := by
    rw [coeff_X_pow_mul', if_pos (by omega), show 3 * (n + 8) + r - 16 = 3 * n + r + 8 by omega]
  rw [h1, hX, map_add, coeff_mul_expand _ _ _ _ hr, coeff_mul_expand _ _ _ _ hr, ← map_add]
  simp only [esem, stepP, lps_trim, lps_ev3]
  congr 1; ring

/-! ## The computable readout `[x^0]` -/

lemma acoefN_eq (D : ℕ) (S : St3) (n : ℕ) (hn : n < D) : acoefN D S n = coeff n (esem S) := by
  have hl : ∀ L : List (ZMod 3), TRep D L (lps L) := fun L m _ => by simp [lps]
  have hT : TRep D (T3L D) T3 := fun m hm => by simp [T3L, T3, lget_map_range _ hm]
  have hQ : TRep D (tinv D 2 Qp3) (lps Qp3)⁻¹ :=
    tinv_rep (hl Qp3) 2 (fun _ => by simp [Qp3, lget]; decide)
  exact tmul_rep (tadd_rep (hl _) (tmul_rep (hl _) hT)) hQ n hn

lemma acoef_eq (S : St3) : acoef S = coeff 8 (esem S) := acoefN_eq 9 S 8 (by norm_num)

/-! ## Vectors of states and reachability -/

lemma vals_step (V : List St3) (n r : ℕ) (hr : r < 3) : vals V (3 * n + r) = vals (stepV r V) n := by
  simp only [vals, stepV, List.map_map]
  exact List.map_congr_left fun S _ => cartier_step S n r hr

lemma vals_zero (V : List St3) : vals V 0 = V.map acoef := by
  simp only [vals, zero_add]
  exact List.map_congr_left fun S _ => (acoef_eq S).symm

lemma vals_read (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) (V : List St3) :
    vals V (Nat.ofDigits 3 ds) = vals (readV ds V) 0 := by
  induction ds generalizing V with
  | nil => simp [readV]
  | cons r ds ih =>
    rw [Nat.ofDigits_cons, readV, show r + 3 * Nat.ofDigits 3 ds = 3 * Nat.ofDigits 3 ds + r by ring,
      vals_step V _ r (hds r (by simp)), ih (fun d hd => hds d (by simp [hd]))]

/-- **Closure ⟹ reachability** (states after a nonzero digit): if the list `A` of vectors is closed
under the three steps (with the transition table `tbl`), then every coefficient of a member of `A` is
the readout of a member of `A`. -/
theorem reach_A (A : List (List St3)) (tbl : List (List ℕ)) (N : ℕ) (hN : A.length = N)
    (h : ∀ s : Fin N, ∀ r : Fin 3, (tbl.getD s []).getD r 0 < N ∧
      stepV r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ vals (A.getD s []) n = vals (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨s, hs, rfl⟩
    · obtain ⟨h1, h2⟩ := h ⟨s, hs⟩ ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩
      rw [show n = 3 * (n / 3) + n % 3 from (Nat.div_add_mod n 3).symm,
        vals_step _ _ _ (Nat.mod_lt _ (by norm_num))]
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact ih (n / 3) (by omega) _ h1

/-- **Closure ⟹ reachability** (states before the first nonzero digit): with `B` closed under the
digit `0` and mapped into `A` by the digits `1, 2`, every coefficient `n ≥ 1` of a member of `B` is the
readout of a member of `A`. -/
theorem reach_B (A B : List (List St3)) (tA tB : List (List ℕ)) (N M : ℕ) (hN : A.length = N)
    (hM : B.length = M)
    (hA : ∀ s : Fin N, ∀ r : Fin 3, (tA.getD s []).getD r 0 < N ∧
      stepV r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepV 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepV r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ vals (B.getD s []) n = vals (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    obtain ⟨⟨h01, h02⟩, h12⟩ := hB ⟨s, hs⟩
    simp only [Fin.val_mk] at h01 h02 h12
    rw [show n = 3 * (n / 3) + n % 3 from (Nat.div_add_mod n 3).symm,
      vals_step _ _ _ (Nat.mod_lt _ (by norm_num))]
    by_cases h0 : n % 3 = 0
    · rw [h0, h02]
      exact ih (n / 3) (by omega) _ (by omega) h01
    · obtain ⟨h1, h2⟩ := h12 ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ (fun h => h0 (by simpa using h))
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact reach_A A tA N hN hA _ _ h1

end GeoSeq
