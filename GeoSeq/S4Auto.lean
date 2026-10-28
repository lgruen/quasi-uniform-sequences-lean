/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.K4Auto
public import GeoSeq.S4Defs

@[expose] public section

/-!
# GeoSeq stage S8: the Artin–Schreier root over `𝔽_4` and the automaton of `thm:S4`

* `lem:frames`(a) for `H = 𝔽_4`: `U = ∑_k x^{4^k}` satisfies the Mahler equation `U(x) = U(x⁴) + x`
  and `U⁴ + U = x` (`S4_frames`).
* The Cartier step on the states (`cartier_stepU`; components mixed by `U(x)^a = (U(x⁴) + x)^a`), the
  computable readout, and closure ⟹ reachability (`reach_AU`, `reach_BU`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## `U` (`lem:frames`(a), `H = 𝔽_4`) -/

/-- `n` is a power of `4`. -/
def IsP4 (n : ℕ) : Prop := ∃ k, 4 ^ k = n

lemma u4_of_isP4 {n : ℕ} (h : IsP4 n) : u4c n = 1 := by
  obtain ⟨k, rfl⟩ := h
  unfold u4c
  rw [if_pos ⟨k, Nat.lt_succ_of_le (Nat.lt_pow_self (by norm_num)).le, rfl⟩]

lemma u4_of_not {n : ℕ} (h : ¬ IsP4 n) : u4c n = 0 := by
  unfold u4c
  rw [if_neg]
  rintro ⟨k, _, hk⟩; exact h ⟨k, hk⟩

lemma not_isP4_zero : ¬ IsP4 0 := by
  rintro ⟨k, hk⟩; exact absurd hk (by positivity)

lemma isP4_one : IsP4 1 := ⟨0, rfl⟩

lemma isP4_quad (m : ℕ) (hm : 1 ≤ m) : IsP4 (4 * m) ↔ IsP4 m := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp at hk; omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [pow_succ]; ring⟩

lemma not_isP4_nd (n : ℕ) (hn : 2 ≤ n) (ho : n % 4 ≠ 0) : ¬ IsP4 n := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · simp at hk; omega
  · rw [pow_succ] at hk; omega

/-- **`lem:frames`(a)**, Mahler equation: `U(x) = U(x⁴) + x`. -/
lemma U4_mahler : U4 = expand 4 four_ne_zero U4 + X := by
  ext n
  rw [map_add, coeff_expand, coeff_X]
  simp only [U4, coeff_mk]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp [u4_of_not not_isP4_zero]
    · simp [u4_of_isP4 isP4_one]
  · rw [if_neg (show ¬ (n = 1) by omega), add_zero]
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      rw [if_pos (dvd_mul_right 4 m), show 4 * m / 4 = m by omega]
      by_cases hp : IsP4 m
      · rw [u4_of_isP4 hp, u4_of_isP4 ((isP4_quad m (by omega)).mpr hp)]
      · rw [u4_of_not hp, u4_of_not (fun h' => hp ((isP4_quad m (by omega)).mp h'))]
    · rw [if_neg h4, u4_of_not (not_isP4_nd n h (fun h' => h4 (Nat.dvd_of_mod_eq_zero h')))]

/-- `U⁴ + U = x`. -/
lemma U4_quart : U4 ^ 4 + U4 = X := by
  have h := U4_mahler
  rw [frob4] at h
  linear_combination h + U4 ^ 4 * ps4_two

lemma U4_coeff1 : coeff 1 U4 = 1 := by
  simp only [U4, coeff_mk]; exact u4_of_isP4 isP4_one

lemma U4_const : constantCoeff U4 = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp only [U4, coeff_mk]; exact u4_of_not not_isP4_zero

/-- **`lem:frames`(a) for `H = 𝔽_4`**: `U = ∑_{k≥0} x^{4^k}` satisfies `U⁴ + U = x`, `U(0) = 0`, the
Mahler equation `U(x) = U(x⁴) + x`, and `[x^n] U = 1` exactly at the powers of `4` (`0` otherwise). -/
theorem S4_frames : U4 ^ 4 + U4 = X ∧ constantCoeff U4 = 0 ∧ U4 = expand 4 four_ne_zero U4 + X ∧
    (∀ k, coeff (4 ^ k) U4 = 1) ∧ ∀ n, ¬ IsP4 n → coeff n U4 = 0 := by
  refine ⟨U4_quart, U4_const, U4_mahler, fun k => ?_, fun n h => ?_⟩
  · simp only [U4, coeff_mk]; exact u4_of_isP4 ⟨k, rfl⟩
  · simp only [U4, coeff_mk]; exact u4_of_not h

/-! ## States of the automaton (`prop:automaton`, Artin–Schreier case, `q = 4`) -/

lemma QpU_const : constantCoeff (lps QpU) = F4.w2 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [lps, QpU, lget]

lemma QpU_unit : lps QpU * (lps QpU)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [QpU_const]; decide)

lemma lps_Q3U : lps Q3U = lps QpU ^ 3 := by
  have e : Q3U = pmul QpU (pmul QpU QpU) := by decide
  rw [e, lps_pmul, lps_pmul]; ring

/-- **The Cartier step** (`prop:automaton`, proof, Artin–Schreier case over `𝔽_4`): for `r < 4`,
coefficient `4n + r` of a state is coefficient `n` of `stepU r` of it. -/
theorem cartier_stepU (S : StU) (n r : ℕ) (hr : r < 4) :
    coeff (4 * n + r + 5) (esemU S) = coeff (n + 5) (esemU (stepU r S)) := by
  set Q := lps QpU
  set Qi := Q⁻¹
  have hQ : Q * Qi = 1 := QpU_unit
  have hQi : Qi = Q ^ 3 * expand 4 four_ne_zero Qi := by
    rw [frob4]; linear_combination (Qi * (1 + Q * Qi + Q ^ 2 * Qi ^ 2)) * hQ.symm
  have hU := U4_mahler
  have h2 := ps4_two
  set E := expand 4 four_ne_zero U4
  have hX : X ^ 15 * esemU S =
      lps (pshift 15 (pmul (padd S.1 (padd (pmul [0, 1] S.2.1)
        (padd (pmul [0, 0, 1] S.2.2.1) (pmul [0, 0, 0, 1] S.2.2.2)))) Q3U)) * expand 4 four_ne_zero Qi +
      lps (pshift 15 (pmul (padd S.2.1 (pmul [0, 0, 1] S.2.2.2)) Q3U)) *
        expand 4 four_ne_zero (U4 * Qi) +
      lps (pshift 15 (pmul (padd S.2.2.1 (pmul [0, 1] S.2.2.2)) Q3U)) *
        expand 4 four_ne_zero (U4 ^ 2 * Qi) +
      lps (pshift 15 (pmul S.2.2.2 Q3U)) * expand 4 four_ne_zero (U4 ^ 3 * Qi) := by
    simp only [lps_pshift, lps_pmul, lps_padd, lps_Q3U, map_mul, map_pow, esemU, tsemU, lps_cons,
      lps_nil, map_zero, map_one, mul_zero, add_zero, zero_add, mul_one]
    linear_combination (X ^ 15 * (lps S.1 + lps S.2.1 * U4 + lps S.2.2.1 * U4 ^ 2 + lps S.2.2.2 * U4 ^ 3)) * hQi +
      (X ^ 15 * Q ^ 3 * expand 4 four_ne_zero Qi * (lps S.2.1 + lps S.2.2.1 * (U4 + E + X) +
        lps S.2.2.2 * (U4 ^ 2 + U4 * (E + X) + (E + X) ^ 2))) * hU +
      (X ^ 15 * Q ^ 3 * expand 4 four_ne_zero Qi * (lps S.2.2.1 * E * X +
        lps S.2.2.2 * (E ^ 2 * X + E * X ^ 2))) * h2
  have h1 : coeff (4 * n + r + 5) (esemU S) = coeff (4 * (n + 5) + r) (X ^ 15 * esemU S) := by
    rw [coeff_X_pow_mul', if_pos (by omega), show 4 * (n + 5) + r - 15 = 4 * n + r + 5 by omega]
  rw [h1, hX, map_add, map_add, map_add, coeff_mul_expand4 _ _ _ _ hr, coeff_mul_expand4 _ _ _ _ hr,
    coeff_mul_expand4 _ _ _ _ hr, coeff_mul_expand4 _ _ _ _ hr, ← map_add, ← map_add, ← map_add]
  simp only [esemU, tsemU, stepU, lps_trim, lps_ev4]
  congr 1; ring

/-! ## The computable readout `[x^0]` -/

lemma UL_rep (D : ℕ) : TRep D ((List.range D).map u4c) U4 := fun m hm => by
  simp [U4, lget_map_range _ hm]

lemma acoefU_eq (S : StU) : acoefU S = coeff 5 (esemU S) := by
  have hl : ∀ L : List F4, TRep 6 L (lps L) := fun L m _ => by simp [lps]
  have hU : TRep 6 UL6 U4 := by
    have e : UL6 = (List.range 6).map u4c := by decide
    rw [e]; exact UL_rep 6
  have hU2 : TRep 6 U2L6 (U4 ^ 2) := by
    have e : U2L6 = tmul 6 UL6 UL6 := by decide
    rw [e, pow_two]; exact tmul_rep hU hU
  have hU3 : TRep 6 U3L6 (U4 ^ 3) := by
    have e : U3L6 = tmul 6 U2L6 UL6 := by decide
    rw [e, pow_succ]; exact tmul_rep hU2 hU
  have hQ : TRep 6 QiU6 (lps QpU)⁻¹ := by
    have e : QiU6 = tinv 6 F4.w QpU := by decide
    rw [e]; exact tinv_rep (hl QpU) F4.w (fun _ => by simp [QpU, lget]; rfl)
  have h := tmul_rep (tadd_rep (hl S.1) (tadd_rep (tmul_rep (hl S.2.1) hU)
    (tadd_rep (tmul_rep (hl S.2.2.1) hU2) (tmul_rep (hl S.2.2.2) hU3)))) hQ
  rw [acoefU, h 5 (by norm_num), esemU, tsemU]
  congr 1; ring

lemma tsemLU_rep (S : StU) : TRep 7 (tsemLU S) (tsemU S) := by
  have hl : ∀ L : List F4, TRep 7 L (lps L) := fun L m _ => by simp [lps]
  have hU : TRep 7 UL7 U4 := by
    have e : UL7 = (List.range 7).map u4c := by decide
    rw [e]; exact UL_rep 7
  have hU2 : TRep 7 U2L7 (U4 ^ 2) := by
    have e : U2L7 = tmul 7 UL7 UL7 := by decide
    rw [e, pow_two]; exact tmul_rep hU hU
  have hU3 : TRep 7 U3L7 (U4 ^ 3) := by
    have e : U3L7 = tmul 7 U2L7 UL7 := by decide
    rw [e, pow_succ]; exact tmul_rep hU2 hU
  have h := tadd_rep (hl S.1) (tadd_rep (tmul_rep (hl S.2.1) hU)
    (tadd_rep (tmul_rep (hl S.2.2.1) hU2) (tmul_rep (hl S.2.2.2) hU3)))
  intro m hm
  rw [tsemLU, h m hm, tsemU]
  congr 1; ring

/-! ## Vectors of states and reachability -/

lemma valsU_step (V : List StU) (n r : ℕ) (hr : r < 4) :
    valsU V (4 * n + r) = valsU (stepVU r V) n := by
  simp only [valsU, stepVU, List.map_map]
  exact List.map_congr_left fun S _ => cartier_stepU S n r hr

lemma valsU_zero (V : List StU) : valsU V 0 = V.map acoefU := by
  simp only [valsU, zero_add]
  exact List.map_congr_left fun S _ => (acoefU_eq S).symm

lemma valsU_read (ds : List ℕ) (hds : ∀ d ∈ ds, d < 4) (V : List StU) :
    valsU V (Nat.ofDigits 4 ds) = valsU (readVU ds V) 0 := by
  induction ds generalizing V with
  | nil => simp [readVU]
  | cons r ds ih =>
    rw [Nat.ofDigits_cons, readVU, show r + 4 * Nat.ofDigits 4 ds = 4 * Nat.ofDigits 4 ds + r by ring,
      valsU_step V _ r (hds r (by simp)), ih (fun d hd => hds d (by simp [hd]))]

/-- **Closure ⟹ reachability** (states after a nonzero digit, `thm:S4`). -/
theorem reach_AU (A : List (List StU)) (tbl : List (List ℕ)) (N : ℕ)
    (h : ∀ s : Fin N, ∀ r : Fin 4, (tbl.getD s []).getD r 0 < N ∧
      stepVU r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ valsU (A.getD s []) n = valsU (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨s, hs, rfl⟩
    · obtain ⟨h1, h2⟩ := h ⟨s, hs⟩ ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩
      rw [show n = 4 * (n / 4) + n % 4 from (Nat.div_add_mod n 4).symm,
        valsU_step _ _ _ (Nat.mod_lt _ (by norm_num))]
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact ih (n / 4) (by omega) _ h1

/-- **Closure ⟹ reachability** (states before the first nonzero digit, `thm:S4`). -/
theorem reach_BU (A B : List (List StU)) (tA tB : List (List ℕ)) (N M : ℕ)
    (hA : ∀ s : Fin N, ∀ r : Fin 4, (tA.getD s []).getD r 0 < N ∧
      stepVU r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepVU 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 4, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepVU r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ valsU (B.getD s []) n = valsU (A.getD s' []) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    obtain ⟨⟨h01, h02⟩, h12⟩ := hB ⟨s, hs⟩
    simp only [Fin.val_mk] at h01 h02 h12
    rw [show n = 4 * (n / 4) + n % 4 from (Nat.div_add_mod n 4).symm,
      valsU_step _ _ _ (Nat.mod_lt _ (by norm_num))]
    by_cases h0 : n % 4 = 0
    · rw [h0, h02]
      exact ih (n / 4) (by omega) _ (by omega) h01
    · obtain ⟨h1, h2⟩ := h12 ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ (fun h => h0 (by simpa using h))
      simp only [Fin.val_mk] at h1 h2
      rw [h2]
      exact reach_AU A tA N hA _ _ h1

end GeoSeq
