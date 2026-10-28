/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B3Auto
public import GeoSeq.S3Defs

@[expose] public section

/-!
# GeoSeq stage S8: the Artin–Schreier root over `𝔽_3` and the automaton of `thm:S3`

* `lem:frames`(a) for `H = 𝔽_3`: `U = -∑_k x^{3^k}` satisfies the Mahler equation `U(x) = U(x³) - x`
  and `U³ - U = x` (`S3_frames`).
* The Cartier step on the states (`cartier_stepS`; the Artin–Schreier case of the proof of
  `prop:automaton`, components mixed by `U(x)^a = (U(x³) - x)^a`), the computable readout, and
  closure ⟹ reachability (`reach_AS`, `reach_BS`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## `U` (`lem:frames`(a), `H = 𝔽_3`) -/

/-- `n` is a power of `3`. -/
def IsP3 (n : ℕ) : Prop := ∃ k, 3 ^ k = n

lemma u3_of_isP3 {n : ℕ} (h : IsP3 n) : u3c n = 2 := by
  obtain ⟨k, rfl⟩ := h
  unfold u3c
  rw [if_pos ⟨k, Nat.lt_succ_of_le (Nat.lt_pow_self (by norm_num)).le, rfl⟩]

lemma u3_of_not {n : ℕ} (h : ¬ IsP3 n) : u3c n = 0 := by
  unfold u3c
  rw [if_neg]
  rintro ⟨k, _, hk⟩; exact h ⟨k, hk⟩

lemma not_isP3_zero : ¬ IsP3 0 := by
  rintro ⟨k, hk⟩; exact absurd hk (by positivity)

lemma isP3_one : IsP3 1 := ⟨0, rfl⟩

lemma isP3_triple (m : ℕ) (hm : 1 ≤ m) : IsP3 (3 * m) ↔ IsP3 m := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp at hk; omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [pow_succ]; ring⟩

lemma not_isP3_nd (n : ℕ) (hn : 2 ≤ n) (ho : n % 3 ≠ 0) : ¬ IsP3 n := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · simp at hk; omega
  · rw [pow_succ] at hk; omega

/-- **`lem:frames`(a)**, Mahler equation: `U(x) = U(x³) - x`. -/
lemma U3_mahler : U3 = expand 3 three_ne_zero U3 - X := by
  ext n
  rw [map_sub, coeff_expand, coeff_X]
  simp only [U3, coeff_mk]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp [u3_of_not not_isP3_zero]; rfl
    · simp [u3_of_isP3 isP3_one]; decide
  · rw [if_neg (show ¬ (n = 1) by omega)]
    refine Eq.trans ?_ (sub_zero _).symm
    by_cases h3 : 3 ∣ n
    · obtain ⟨m, rfl⟩ := h3
      rw [if_pos (dvd_mul_right 3 m), show 3 * m / 3 = m by omega]
      by_cases hp : IsP3 m
      · rw [u3_of_isP3 hp, u3_of_isP3 ((isP3_triple m (by omega)).mpr hp)]
      · rw [u3_of_not hp, u3_of_not (fun h' => hp ((isP3_triple m (by omega)).mp h'))]
    · rw [if_neg h3, u3_of_not (not_isP3_nd n h (fun h' => h3 (Nat.dvd_of_mod_eq_zero h')))]

/-- `U³ - U = x`. -/
lemma U3_cube : U3 ^ 3 - U3 = X := by
  have h := U3_mahler
  rw [frob3] at h
  linear_combination -h

lemma U3_coeff1 : coeff 1 U3 = 2 := by
  simp only [U3, coeff_mk]; exact u3_of_isP3 isP3_one

lemma U3_const : constantCoeff U3 = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp only [U3, coeff_mk]; exact u3_of_not not_isP3_zero

/-- **`lem:frames`(a) for `H = 𝔽_3`**: `U = -∑_{k≥0} x^{3^k}` satisfies `U³ - U = x`, `U(0) = 0`, the
Mahler equation `U(x) = U(x³) - x`, and `[x^n] U = -1` exactly at the powers of `3` (`0` otherwise). -/
theorem S3_frames : U3 ^ 3 - U3 = X ∧ constantCoeff U3 = 0 ∧ U3 = expand 3 three_ne_zero U3 - X ∧
    (∀ k, coeff (3 ^ k) U3 = -1) ∧ ∀ n, ¬ IsP3 n → coeff n U3 = 0 := by
  refine ⟨U3_cube, U3_const, U3_mahler, fun k => ?_, fun n h => ?_⟩
  · simp only [U3, coeff_mk]; rw [u3_of_isP3 ⟨k, rfl⟩]; rfl
  · simp only [U3, coeff_mk]; exact u3_of_not h

/-! ## States of the automaton (`prop:automaton`, Artin–Schreier case, `q = 3`) -/

lemma QpS_const : constantCoeff (lps QpS) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [lps, QpS, lget]

lemma QpS_unit : lps QpS * (lps QpS)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [QpS_const]; exact one_ne_zero)

lemma lps_QQS : lps QQS = lps QpS ^ 2 := by
  have e : QQS = pmul QpS QpS := by decide
  rw [e, lps_pmul]; ring

/-- **The Cartier step** (`prop:automaton`, proof, Artin–Schreier case): for `r < 3`, coefficient
`3n + r` of a state is coefficient `n` of `stepS r` of it. -/
theorem cartier_stepS (S : StS) (n r : ℕ) (hr : r < 3) :
    coeff (3 * n + r + 8) (esemS S) = coeff (n + 8) (esemS (stepS r S)) := by
  set Q := lps QpS
  set Qi := Q⁻¹
  have hQ : Q * Qi = 1 := QpS_unit
  have hQi : Qi = Q ^ 2 * expand 3 three_ne_zero Qi := by
    rw [frob3]; linear_combination (Qi * (1 + Q * Qi)) * hQ.symm
  have hU := U3_mahler
  have h3 := ps3_three
  set E := expand 3 three_ne_zero U3
  have hX : X ^ 16 * esemS S =
      lps (pshift 16 (pmul (padd S.1 (padd (pmul [0, 2] S.2.1) (pmul [0, 0, 1] S.2.2))) QQS)) *
        expand 3 three_ne_zero Qi +
      lps (pshift 16 (pmul (padd S.2.1 (pmul [0, 1] S.2.2)) QQS)) * expand 3 three_ne_zero (U3 * Qi) +
      lps (pshift 16 (pmul S.2.2 QQS)) * expand 3 three_ne_zero (U3 ^ 2 * Qi) := by
    simp only [lps_pshift, lps_pmul, lps_padd, lps_QQS, map_mul, map_pow, esemS, tsemS, lps_cons,
      lps_nil, map_zero, map_one, map_ofNat, mul_zero, add_zero, zero_add, mul_one]
    linear_combination (X ^ 16 * (lps S.1 + lps S.2.1 * U3 + lps S.2.2 * U3 ^ 2)) * hQi +
      (X ^ 16 * Q ^ 2 * expand 3 three_ne_zero Qi * (lps S.2.1 + lps S.2.2 * (U3 + E - X))) * hU -
      (X ^ 16 * Q ^ 2 * expand 3 three_ne_zero Qi * X * (lps S.2.1 + lps S.2.2 * E)) * h3
  have h1 : coeff (3 * n + r + 8) (esemS S) = coeff (3 * (n + 8) + r) (X ^ 16 * esemS S) := by
    rw [coeff_X_pow_mul', if_pos (by omega), show 3 * (n + 8) + r - 16 = 3 * n + r + 8 by omega]
  rw [h1, hX, map_add, map_add, coeff_mul_expand _ _ _ _ hr, coeff_mul_expand _ _ _ _ hr,
    coeff_mul_expand _ _ _ _ hr, ← map_add, ← map_add]
  simp only [esemS, tsemS, stepS, lps_trim, lps_ev3]
  congr 1; ring

/-! ## The computable readout `[x^0]` -/

lemma UL3_rep (D : ℕ) : TRep D (UL3 D) U3 := fun m hm => by simp [UL3, U3, lget_map_range _ hm]

lemma tsemLS_rep (D : ℕ) (S : StS) : TRep D (tsemLS D S) (tsemS S) := by
  have hl : ∀ L : List (ZMod 3), TRep D L (lps L) := fun L m _ => by simp [lps]
  have h := tadd_rep (hl S.1) (tadd_rep (tmul_rep (hl S.2.1) (UL3_rep D))
    (tmul_rep (hl S.2.2) (tmul_rep (UL3_rep D) (UL3_rep D))))
  intro m hm
  rw [tsemLS, h m hm, tsemS, pow_two, add_assoc]

lemma acoefNS_eq (D : ℕ) (S : StS) (n : ℕ) (hn : n < D) : acoefNS D S n = coeff n (esemS S) := by
  have hl : ∀ L : List (ZMod 3), TRep D L (lps L) := fun L m _ => by simp [lps]
  have hQ : TRep D (tinv D 1 QpS) (lps QpS)⁻¹ :=
    tinv_rep (hl QpS) 1 (fun _ => by simp [QpS, lget])
  exact tmul_rep (tsemLS_rep D S) hQ n hn

lemma acoefS_eq (S : StS) : acoefS S = coeff 8 (esemS S) := by
  have hl : ∀ L : List (ZMod 3), TRep 9 L (lps L) := fun L m _ => by simp [lps]
  have hU : TRep 9 UL9 U3 := by
    have e : UL9 = UL3 9 := by decide
    rw [e]; exact UL3_rep 9
  have hU2 : TRep 9 U2L9 (U3 ^ 2) := by
    have e : U2L9 = tmul 9 (UL3 9) (UL3 9) := by decide
    rw [e, pow_two]; exact tmul_rep (UL3_rep 9) (UL3_rep 9)
  have hQ : TRep 9 QiS9 (lps QpS)⁻¹ := by
    have e : QiS9 = tinv 9 1 QpS := by decide
    rw [e]; exact tinv_rep (hl QpS) 1 (fun _ => by simp [QpS, lget])
  have h := tmul_rep (tadd_rep (hl S.1) (tadd_rep (tmul_rep (hl S.2.1) hU) (tmul_rep (hl S.2.2) hU2))) hQ
  rw [acoefS, h 8 (by norm_num), esemS, tsemS, add_assoc]

/-! ## Vectors of states and reachability -/

lemma valsS_step (V : List StS) (n r : ℕ) (hr : r < 3) :
    valsS V (3 * n + r) = valsS (stepVS r V) n := by
  simp only [valsS, stepVS, List.map_map]
  exact List.map_congr_left fun S _ => cartier_stepS S n r hr

lemma valsS_zero (V : List StS) : valsS V 0 = V.map acoefS := by
  simp only [valsS, zero_add]
  exact List.map_congr_left fun S _ => (acoefS_eq S).symm

lemma valsS_read (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) (V : List StS) :
    valsS V (Nat.ofDigits 3 ds) = valsS (readVS ds V) 0 := by
  induction ds generalizing V with
  | nil => simp [readVS]
  | cons r ds ih =>
    rw [Nat.ofDigits_cons, readVS, show r + 3 * Nat.ofDigits 3 ds = 3 * Nat.ofDigits 3 ds + r by ring,
      valsS_step V _ r (hds r (by simp)), ih (fun d hd => hds d (by simp [hd]))]

/-- **Closure ⟹ reachability** (states after a nonzero digit, `thm:S3`). -/
theorem reach_AS (A : List (List StS)) (tbl : List (List ℕ)) (N : ℕ)
    (h : ∀ s : Fin N, ∀ r : Fin 3, (tbl.getD s []).getD r 0 < N ∧
      stepVS r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ valsS (A.getD s []) n = valsS (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨s, hs, rfl⟩
    · obtain ⟨h1, h2⟩ := h ⟨s, hs⟩ ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩
      rw [show n = 3 * (n / 3) + n % 3 from (Nat.div_add_mod n 3).symm,
        valsS_step _ _ _ (Nat.mod_lt _ (by norm_num))]
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact ih (n / 3) (by omega) _ h1

/-- **Closure ⟹ reachability** (states before the first nonzero digit, `thm:S3`). -/
theorem reach_BS (A B : List (List StS)) (tA tB : List (List ℕ)) (N M : ℕ)
    (hA : ∀ s : Fin N, ∀ r : Fin 3, (tA.getD s []).getD r 0 < N ∧
      stepVS r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepVS 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepVS r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ valsS (B.getD s []) n = valsS (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    obtain ⟨⟨h01, h02⟩, h12⟩ := hB ⟨s, hs⟩
    simp only [Fin.val_mk] at h01 h02 h12
    rw [show n = 3 * (n / 3) + n % 3 from (Nat.div_add_mod n 3).symm,
      valsS_step _ _ _ (Nat.mod_lt _ (by norm_num))]
    by_cases h0 : n % 3 = 0
    · rw [h0, h02]
      exact ih (n / 3) (by omega) _ (by omega) h01
    · obtain ⟨h1, h2⟩ := h12 ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ (fun h => h0 (by simpa using h))
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact reach_AS A tA N hA _ _ h1

end GeoSeq
