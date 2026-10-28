/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B3Auto
public import GeoSeq.K4Defs

@[expose] public section

/-!
# GeoSeq stage S8: the Kummer root over `𝔽_4` and Cartier operators in base `4`

* `lem:frames`(b) for `q = 4`: `T4 = τ^{-1}` satisfies the Mahler equation `T4(x) = (1 + x) T4(x⁴)`,
  `τ³ = 1 + x`, and `[x^n] T4 = 1` iff every base-4 digit of `n` is `0` or `1` (`K4_frames`).
* The Cartier operators `Λ_r` in base `4` (`lam4`) and `[x^{4m+r}] N(x) A(x⁴) = [x^m] Λ_r(N) A`.
* The Cartier step on the states of `prop:automaton` (`cartier_step4`), the computable readout
  (`acoef4_eq`), and closure ⟹ reachability (`reach_A4`, `reach_B4`), as in stage S6 for `q = 3`.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Lists: the Cartier selection in base `4` -/

section Lists

variable {R : Type*} [CommRing R]

lemma lget_ev4 (k : ℕ) (L : List R) (n : ℕ) : lget (ev4 k L) n = lget L (k + 4 * n) := by
  induction L generalizing k n with
  | nil => simp [ev4, lget_nil']
  | cons x r ih =>
    rcases k with _ | k
    · rcases n with _ | n
      · simp [ev4, lget_cons0]
      · simp only [ev4, lget_cons_succ]
        rw [ih 3 n, show 0 + 4 * (n + 1) = (3 + 4 * n) + 1 by ring, lget_cons_succ]
    · simp only [ev4]
      rw [ih k n, show k + 1 + 4 * n = (k + 4 * n) + 1 by ring, lget_cons_succ]

lemma lps_ev4 (r : ℕ) (L : List R) : lps (ev4 r L) = lam4 r (lps L) := by
  ext n; simp [lps, lam4, lget_ev4, add_comm]

end Lists

/-! ## `𝔽_4`: characteristic two and Frobenius -/

lemma f4_card : Fintype.card F4 = 4 := rfl

lemma ps4_two : (2 : PowerSeries F4) = 0 := by
  rw [show (2 : PowerSeries F4) = C (2 : F4) from (map_ofNat C 2).symm]
  rw [show (2 : F4) = 0 from rfl, map_zero]

/-- In `𝔽_4[[x]]`, `-a = a`. -/
lemma neg4 (a : PowerSeries F4) : -a = a := by
  have h : a + a = 0 := by linear_combination a * ps4_two
  exact neg_eq_of_add_eq_zero_right h

/-- Frobenius over `𝔽_4`: `F(x⁴) = F(x)⁴`. -/
lemma frob4 (F : PowerSeries F4) : expand 4 four_ne_zero F = F ^ 4 := by
  convert FiniteField.PowerSeries.expand_card F <;> exact f4_card.symm

/-! ## The Kummer root `T4 = τ^{-1}` (`lem:frames`(b), `q = 4`) -/

lemma t4cAux_congr : ∀ (f f' n : ℕ), n ≤ f → n ≤ f' → t4cAux f n = t4cAux f' n := by
  intro f
  induction f with
  | zero =>
    intro f' n hn _
    obtain rfl : n = 0 := by omega
    cases f' <;> simp [t4cAux]
  | succ f ih =>
    intro f' n hn hn'
    rcases f' with _ | f'
    · obtain rfl : n = 0 := by omega
      simp [t4cAux]
    · simp only [t4cAux]
      by_cases h0 : n = 0
      · simp [h0]
      · rw [ih f' (n / 4) (by omega) (by omega)]

/-- The digit recursion of `t4c`. -/
lemma t4c_rec (n : ℕ) :
    t4c n = if n = 0 then 1 else if 2 ≤ n % 4 then 0 else t4c (n / 4) := by
  rcases n with _ | m
  · simp [t4c, t4cAux]
  · unfold t4c
    simp only [t4cAux, Nat.add_one_ne_zero, ite_false]
    rw [t4cAux_congr m ((m + 1) / 4) _ (by omega) le_rfl]

/-- **`lem:frames`(b)**, Mahler equation: `T4(x) = (1 + x) T4(x⁴)`. -/
lemma T4_mahler : T4 = (1 + X) * expand 4 four_ne_zero T4 := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_expand]
  rcases n with _ | m
  · simp [T4, t4c, t4cAux]
  · rw [coeff_succ_X_mul, coeff_expand]
    simp only [T4, coeff_mk]
    rw [t4c_rec (m + 1)]
    simp only [Nat.add_one_ne_zero, ite_false]
    have h4 : (m + 1) % 4 = 0 ∨ (m + 1) % 4 = 1 ∨ (m + 1) % 4 = 2 ∨ (m + 1) % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), add_zero]
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), zero_add]
      congr 1; omega
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), add_zero]
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), add_zero]

lemma T4_const : constantCoeff T4 = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [T4, t4c, t4cAux]

lemma T4_cube : (1 + X) * T4 ^ 3 = 1 := by
  have hm := T4_mahler
  rw [frob4] at hm
  have hne : T4 ≠ 0 := fun h => by
    have := T4_const; rw [h, map_zero] at this; exact zero_ne_one this
  have h : T4 * ((1 + X) * T4 ^ 3 - 1) = 0 := by linear_combination -hm
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

lemma tau4_T4 : tau4 * T4 = 1 :=
  PowerSeries.inv_mul_cancel _ (by rw [T4_const]; exact one_ne_zero)

lemma tau4_const : constantCoeff tau4 = 1 := by
  have h := congrArg constantCoeff tau4_T4
  rw [map_mul, T4_const, mul_one, map_one] at h
  exact h

/-- `τ³ = 1 + x`. -/
lemma tau4_cube : tau4 ^ 3 = 1 + X := by
  have h1 := tau4_T4
  have h2 := T4_cube
  linear_combination (1 + X) * (tau4 ^ 2 * T4 ^ 2 + tau4 * T4 + 1) * h1 - tau4 ^ 3 * h2

/-- The digit rule of `lem:frames`(b), `q = 4`. -/
lemma t4c_digits (n : ℕ) : t4c n = if ∀ d ∈ Nat.digits 4 n, d ≤ 1 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [t4c, t4cAux]
    · rw [t4c_rec, if_neg (by omega), Nat.digits_def' (by norm_num) hn]
      by_cases h2 : 2 ≤ n % 4
      · rw [if_pos h2, if_neg]; intro h; have := h (n % 4) (by simp); omega
      · rw [if_neg h2, ih (n / 4) (by omega)]
        have hle : n % 4 ≤ 1 := by omega
        by_cases hall : ∀ d ∈ Nat.digits 4 (n / 4), d ≤ 1
        · rw [if_pos hall, if_pos]
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hle
          · exact hall d hd
        · rw [if_neg hall, if_neg]
          intro h; exact hall fun d hd => h d (List.mem_cons_of_mem _ hd)

/-- **`lem:frames`(b) for `q = 4`**: `τ` (with `τ^{-1} = T4 = ∏_{i≥0}(1 + x^{4^i})`) satisfies
`τ³ = 1 + x`, `τ(0) = 1`; `T4` satisfies the Mahler equation `T4(x) = (1 + x) T4(x⁴)`, and
`[x^n] T4 = 1` exactly when every base-4 digit of `n` is `0` or `1` (`0` otherwise). -/
theorem K4_frames : tau4 * T4 = 1 ∧ tau4 ^ 3 = 1 + X ∧ constantCoeff tau4 = 1 ∧
    T4 = (1 + X) * expand 4 four_ne_zero T4 ∧
    ∀ n, coeff n T4 = if ∀ d ∈ Nat.digits 4 n, d ≤ 1 then 1 else 0 :=
  ⟨tau4_T4, tau4_cube, tau4_const, T4_mahler, fun n => by rw [T4, coeff_mk, t4c_digits]⟩

/-! ## The Cartier operators in base `4` -/

section Cartier

variable {R : Type*} [CommRing R]

lemma coeff_Xpow_expand4 (r n : ℕ) (F : PowerSeries R) :
    coeff n (X ^ r * expand 4 four_ne_zero F) =
      if r ≤ n ∧ 4 ∣ (n - r) then coeff ((n - r) / 4) F else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : r ≤ n
  · simp [h]
  · simp [h]

lemma decomp4 (N : PowerSeries R) :
    N = ∑ r ∈ range 4, X ^ r * expand 4 four_ne_zero (lam4 r N) := by
  ext n
  rw [map_sum, Finset.sum_eq_single (n % 4)]
  · rw [coeff_Xpow_expand4, if_pos ⟨Nat.mod_le n 4, Nat.dvd_sub_mod n⟩, lam4, coeff_mk]
    rw [show 4 * ((n - n % 4) / 4) + n % 4 = n by omega]
  · intro r hr hne
    rw [coeff_Xpow_expand4, if_neg]
    rintro ⟨h1, d, hd⟩
    have := Finset.mem_range.mp hr
    omega
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.mod_lt n (by norm_num))) h

lemma coeff_mul_expand4 (N A : PowerSeries R) (m r : ℕ) (hr : r < 4) :
    coeff (4 * m + r) (N * expand 4 four_ne_zero A) = coeff m (lam4 r N * A) := by
  conv_lhs => rw [decomp4 N]
  have e : ∀ r', X ^ r' * expand 4 four_ne_zero (lam4 r' N) * expand 4 four_ne_zero A =
      X ^ r' * expand 4 four_ne_zero (lam4 r' N * A) := fun r' => by rw [map_mul]; ring
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single r]
  · rw [e, coeff_Xpow_expand4, if_pos ⟨by omega, ⟨m, by omega⟩⟩]
    rw [show (4 * m + r - r) / 4 = m by omega]
  · intro r' hr' hne
    rw [e, coeff_Xpow_expand4, if_neg]
    rintro ⟨h1, d, hd⟩
    have := Finset.mem_range.mp hr'
    omega
  · intro h; exact absurd (Finset.mem_range.mpr hr) h

end Cartier

/-! ## States of the automaton (`prop:automaton`, Kummer case, `q = 4`) -/

lemma Qp4_const : constantCoeff (lps Qp4) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [lps, Qp4, lget]

lemma Qp4_unit : lps Qp4 * (lps Qp4)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [Qp4_const]; exact one_ne_zero)

lemma lps_W40 : lps (W4 0) = lps Qp4 ^ 3 := by
  have e : W4 0 = pmul Qp4 (pmul Qp4 Qp4) := by decide
  rw [e, lps_pmul, lps_pmul]; ring

lemma lps_W41 : lps (W4 1) = lps Qp4 ^ 3 * (1 + X) := by
  have e : W4 1 = pmul (W4 0) [1, 1] := by decide
  rw [e, lps_pmul, lps_W40]
  congr 1
  rw [lps_cons, lps_cons, lps_nil]; simp

lemma lps_Qp4 : lps Qp4 = (1 + X) ^ 2 := by
  simp only [Qp4, lps_cons, lps_nil, map_one, map_zero, mul_zero, add_zero, zero_add]
  linear_combination (-X) * ps4_two

lemma lps_W42 : lps (W4 2) = lps Qp4 ^ 3 * (1 + X) ^ 2 := by
  have e : W4 2 = pmul (W4 0) Qp4 := by decide
  rw [e, lps_pmul, lps_W40, lps_Qp4]

/-- **The Cartier step** (`prop:automaton`, proof, `q = 4`): for `r < 4`, coefficient `4n + r` of a
state is coefficient `n` of `stepP4 r` of it. -/
theorem cartier_step4 (S : St4) (n r : ℕ) (hr : r < 4) :
    coeff (4 * n + r + 8) (esem4 S) = coeff (n + 8) (esem4 (stepP4 r S)) := by
  set Q := lps Qp4
  set Qi := Q⁻¹
  have hQ : Q * Qi = 1 := Qp4_unit
  have hQi : Qi = Q ^ 3 * expand 4 four_ne_zero Qi := by
    rw [frob4]; linear_combination (Qi * (1 + Q * Qi + Q ^ 2 * Qi ^ 2)) * hQ.symm
  have hT := T4_mahler
  set E := expand 4 four_ne_zero T4
  have hX : X ^ 24 * esem4 S =
      lps (pshift 24 (pmul S.1 (W4 0))) * expand 4 four_ne_zero Qi +
      lps (pshift 24 (pmul S.2.1 (W4 1))) * expand 4 four_ne_zero (T4 * Qi) +
      lps (pshift 24 (pmul S.2.2 (W4 2))) * expand 4 four_ne_zero (T4 ^ 2 * Qi) := by
    rw [lps_pshift, lps_pshift, lps_pshift, lps_pmul, lps_pmul, lps_pmul, lps_W40, lps_W41, lps_W42,
      map_mul, map_mul, map_pow, esem4, tsem4]
    linear_combination (X ^ 24 * (lps S.1 + lps S.2.1 * T4 + lps S.2.2 * T4 ^ 2)) * hQi +
      (X ^ 24 * Q ^ 3 * expand 4 four_ne_zero Qi *
        (lps S.2.1 + lps S.2.2 * (T4 + (1 + X) * E))) * hT
  have h1 : coeff (4 * n + r + 8) (esem4 S) = coeff (4 * (n + 8) + r) (X ^ 24 * esem4 S) := by
    rw [coeff_X_pow_mul', if_pos (by omega), show 4 * (n + 8) + r - 24 = 4 * n + r + 8 by omega]
  rw [h1, hX, map_add, map_add, coeff_mul_expand4 _ _ _ _ hr, coeff_mul_expand4 _ _ _ _ hr,
    coeff_mul_expand4 _ _ _ _ hr, ← map_add, ← map_add]
  simp only [esem4, tsem4, stepP4, lps_trim, lps_ev4]
  congr 1; ring

/-! ## The computable readout `[x^0]` -/

lemma T4L_rep (D : ℕ) : TRep D (T4L D) T4 := fun m hm => by simp [T4L, T4, lget_map_range _ hm]

lemma tsemL_rep (D : ℕ) (S : St4) : TRep D (tsemL D S) (tsem4 S) := by
  have hl : ∀ L : List F4, TRep D L (lps L) := fun L m _ => by simp [lps]
  have h := tadd_rep (hl S.1) (tadd_rep (tmul_rep (hl S.2.1) (T4L_rep D))
    (tmul_rep (hl S.2.2) (tmul_rep (T4L_rep D) (T4L_rep D))))
  intro m hm
  rw [tsemL, h m hm, tsem4, pow_two, add_assoc]

lemma acoefN4_eq (D : ℕ) (S : St4) (n : ℕ) (hn : n < D) : acoefN4 D S n = coeff n (esem4 S) := by
  have hl : ∀ L : List F4, TRep D L (lps L) := fun L m _ => by simp [lps]
  have hQ : TRep D (tinv D 1 Qp4) (lps Qp4)⁻¹ :=
    tinv_rep (hl Qp4) 1 (fun _ => by simp [Qp4, lget])
  exact tmul_rep (tsemL_rep D S) hQ n hn

lemma acoef4_eq (S : St4) : acoef4 S = coeff 8 (esem4 S) := acoefN4_eq 9 S 8 (by norm_num)

/-! ## Vectors of states and reachability -/

lemma vals4_step (V : List St4) (n r : ℕ) (hr : r < 4) :
    vals4 V (4 * n + r) = vals4 (stepV4 r V) n := by
  simp only [vals4, stepV4, List.map_map]
  exact List.map_congr_left fun S _ => cartier_step4 S n r hr

lemma vals4_zero (V : List St4) : vals4 V 0 = V.map acoef4 := by
  simp only [vals4, zero_add]
  exact List.map_congr_left fun S _ => (acoef4_eq S).symm

lemma vals4_read (ds : List ℕ) (hds : ∀ d ∈ ds, d < 4) (V : List St4) :
    vals4 V (Nat.ofDigits 4 ds) = vals4 (readV4 ds V) 0 := by
  induction ds generalizing V with
  | nil => simp [readV4]
  | cons r ds ih =>
    rw [Nat.ofDigits_cons, readV4, show r + 4 * Nat.ofDigits 4 ds = 4 * Nat.ofDigits 4 ds + r by ring,
      vals4_step V _ r (hds r (by simp)), ih (fun d hd => hds d (by simp [hd]))]

/-- **Closure ⟹ reachability** (states after a nonzero digit, `q = 4`). -/
theorem reach_A4 (A : List (List St4)) (tbl : List (List ℕ)) (N : ℕ) (hN : A.length = N)
    (h : ∀ s : Fin N, ∀ r : Fin 4, (tbl.getD s []).getD r 0 < N ∧
      stepV4 r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ vals4 (A.getD s []) n = vals4 (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨s, hs, rfl⟩
    · obtain ⟨h1, h2⟩ := h ⟨s, hs⟩ ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩
      rw [show n = 4 * (n / 4) + n % 4 from (Nat.div_add_mod n 4).symm,
        vals4_step _ _ _ (Nat.mod_lt _ (by norm_num))]
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact ih (n / 4) (by omega) _ h1

/-- **Closure ⟹ reachability** (states before the first nonzero digit, `q = 4`). -/
theorem reach_B4 (A B : List (List St4)) (tA tB : List (List ℕ)) (N M : ℕ) (hN : A.length = N)
    (hM : B.length = M)
    (hA : ∀ s : Fin N, ∀ r : Fin 4, (tA.getD s []).getD r 0 < N ∧
      stepV4 r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepV4 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 4, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepV4 r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ vals4 (B.getD s []) n = vals4 (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    obtain ⟨⟨h01, h02⟩, h12⟩ := hB ⟨s, hs⟩
    simp only [Fin.val_mk] at h01 h02 h12
    rw [show n = 4 * (n / 4) + n % 4 from (Nat.div_add_mod n 4).symm,
      vals4_step _ _ _ (Nat.mod_lt _ (by norm_num))]
    by_cases h0 : n % 4 = 0
    · rw [h0, h02]
      exact ih (n / 4) (by omega) _ (by omega) h01
    · obtain ⟨h1, h2⟩ := h12 ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ (fun h => h0 (by simpa using h))
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact reach_A4 A tA N hN hA _ _ h1

end GeoSeq
