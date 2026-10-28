/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S3Auto
public import GeoSeq.B3Law

@[expose] public section

/-!
# GeoSeq stage S8: the law of the Artin–Schreier sequence over `𝔽_3` (`thm:S3`)

* `S3_roots`, `S3_frame_inv`, `S3_law`: `prop:law` applies (`w = z³ - z`, `θ = 1`;
  `G = T^{-1} A^{-1} g^{-1}`).
* `S3_net`: `t = 0` (`lem:t0` via `ss_t0`; places `0, 1, 2`, `g(0) = 1`, `[x] z_c = -1`);
  `S3_faure`: the sequence is a scramble `(L_0 P_0, L_1 P_1, L_2 P_2)` of the Faure sequence.
* Closed forms in the basis `{1, U, U²}` (`U³ = U + x`): `(1 - x) M[c][b] = S3Mn c b` (`S3_M`),
  `x Q_p Ĝ[b][c'] = S3An b c'` (`S3_ghat`; from `1/(1 + x - U) = ((1 + x - U)² + 2)/(x(1 + x²))`).
* The initial states: `esemS (initSS i c c') = x^{8-i} F_i[c][c']`, and coefficient `l` of the state is
  the response `D_i(l)[c][c']` (`S3_init`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## The multiplier and the law -/

lemma S3g_x : (1 - X) * S3g = 1 + X - U3 := by
  have h := PowerSeries.mul_inv_cancel (1 - X : PowerSeries (ZMod 3))
    (by rw [map_sub, map_one, constantCoeff_X]; decide)
  unfold S3g
  linear_combination (1 + X - U3) * h

lemma S3g_const : constantCoeff S3g = 1 := by
  have h := congrArg constantCoeff S3g_x
  rw [map_mul, map_sub, map_one, constantCoeff_X, map_sub, map_add, map_one, constantCoeff_X,
    U3_const] at h
  generalize constantCoeff S3g = t at h ⊢
  revert t h; decide

lemma S3g_inv : S3g * S3g⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [S3g_const]; exact one_ne_zero)


lemma S3Gp00 : S3Gp 0 0 = 1 + 2 * U3 ^ 2 := rfl
lemma S3Gp01 : S3Gp 0 1 = U3 + 2 * U3 ^ 2 := rfl
lemma S3Gp02 : S3Gp 0 2 = 2 * U3 + 2 * U3 ^ 2 := rfl
lemma S3Gp10 : S3Gp 1 0 = 2 * U3 := rfl
lemma S3Gp11 : S3Gp 1 1 = 2 + 2 * U3 := rfl
lemma S3Gp12 : S3Gp 1 2 = 1 + 2 * U3 := rfl
lemma S3Gp20 : S3Gp 2 0 = 2 := rfl
lemma S3Gp21 : S3Gp 2 1 = 2 := rfl
lemma S3Gp22 : S3Gp 2 2 = 2 := rfl
lemma S3Mn00 : S3Mn 0 0 = ([1, 1], [2], []) := rfl
lemma S3Mn01 : S3Mn 0 1 = ([], [1, 1], [2]) := rfl
lemma S3Mn02 : S3Mn 0 2 = ([0, 2], [2], [1, 1]) := rfl
lemma S3Mn10 : S3Mn 1 0 = ([1, 1], [2], []) := rfl
lemma S3Mn11 : S3Mn 1 1 = ([1, 1], [0, 1], [2]) := rfl
lemma S3Mn12 : S3Mn 1 2 = ([1], [0, 2], [2, 1]) := rfl
lemma S3Mn20 : S3Mn 2 0 = ([1, 1], [2], []) := rfl
lemma S3Mn21 : S3Mn 2 1 = ([2, 2], [2, 1], [2]) := rfl
lemma S3Mn22 : S3Mn 2 2 = ([1], [2, 1], [0, 1]) := rfl
lemma S3An00 : S3An 0 0 = ([0, 1, 2], [0, 2, 1], [0, 1, 1, 1]) := rfl
lemma S3An01 : S3An 0 1 = ([0, 0, 2, 1], [0, 0, 1, 2], [0, 2, 0, 1]) := rfl
lemma S3An02 : S3An 0 2 = ([0, 1, 1, 1], [1, 1, 0, 1], [1, 2, 2, 1]) := rfl
lemma S3An10 : S3An 1 0 = ([0, 2, 1], [2, 2, 1, 1], [2, 0, 1]) := rfl
lemma S3An11 : S3An 1 1 = ([0, 0, 2, 1], [1, 2, 2, 1], [1, 1, 1]) := rfl
lemma S3An12 : S3An 1 2 = ([0, 1, 0, 2], [0, 2, 0, 1], [0, 2, 1]) := rfl
lemma S3An20 : S3An 2 0 = ([0, 1, 1, 1], [2, 0, 1], [2, 1]) := rfl
lemma S3An21 : S3An 2 1 = ([0, 1, 1, 1], [2, 0, 1], [2, 1]) := rfl
lemma S3An22 : S3An 2 2 = ([0, 1, 1, 1], [2, 0, 1], [2, 1]) := rfl

/-- In `𝔽_3[[x]]`, `a - b = a + 2b` (used to remove subtractions before `grind`). -/
lemma sub3 (a b : PowerSeries (ZMod 3)) : a - b = a + 2 * b :=
  (sub_eq_add_neg a b).trans (congrArg (a + ·) (neg3 b))

/-- `U³ = U + x` without powers (for `grind`). -/
lemma U3_cube' : U3 * (U3 * U3) = U3 + X := by
  linear_combination U3_cube

/-- `w = z³ - z = z³ + 2z` over `𝔽_3`. -/
lemma S3_roots (c : Fin 3) :
    Polynomial.aeval (S3z c) (Polynomial.X ^ 3 + 2 * Polynomial.X : Polynomial (ZMod 3)) =
      PowerSeries.C (1 : ZMod 3) * X := by
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_one, one_mul, map_ofNat, S3z]
  have hc : (C ((c : ℕ) : ZMod 3) : PowerSeries (ZMod 3)) ^ 3 = C ((c : ℕ) : ZMod 3) := by
    rw [← map_pow]; congr 1; fin_cases c <;> decide
  linear_combination hc + U3_cube +
    (C ((c : ℕ) : ZMod 3) * U3 * (C ((c : ℕ) : ZMod 3) + U3) + C ((c : ℕ) : ZMod 3) + U3) * ps3_three

lemma S3_wdeg : (Polynomial.X ^ 3 + 2 * Polynomial.X : Polynomial (ZMod 3)).natDegree ≤ 3 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by rw [Polynomial.natDegree_X_pow])
      ((Polynomial.natDegree_mul_le).trans (by
        rw [Polynomial.natDegree_X]
        have : (2 : Polynomial (ZMod 3)).natDegree = 0 := Polynomial.natDegree_ofNat 2
        omega)))

/-- **`thm:S3`**: `M G = 1` for the frame matrix `M[c][b] = g (c + U)^b` and `G = S3G`. -/
theorem S3_frame_inv : frameM (fun _ => S3g) S3z * S3G = 1 := by
  have hgi := S3g_inv
  have h3 := ps3_three
  ext1 c c'
  rw [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  fin_cases c <;> fin_cases c' <;>
    simp only [frameM, S3z, S3G, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, S3Gp00, S3Gp01, S3Gp02, S3Gp10, S3Gp11, S3Gp12, S3Gp20, S3Gp21, S3Gp22,
      Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, map_zero,
      map_one, map_ofNat, zero_add, pow_zero, pow_one, pow_two, mul_one, ite_true, ite_false,
      Fin.reduceEq] <;>
    (generalize S3g⁻¹ = gi at hgi ⊢; generalize S3g = g at hgi ⊢; grind)

/-- **`thm:S3`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the sequence is `lawD (fun _ => g) z G i l c c'` (independent of `K`). -/
theorem S3_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 3) :
    IsCarryEntry S3gen K i l c c' (lawD (fun _ => S3g) S3z S3G i l c c') :=
  law (fun _ => S3g) S3z _ S3_wdeg 1 1 (one_mul 1) S3_roots S3G S3_frame_inv K i l hl hlK c c'

/-! ## `t = 0` and the Faure form -/

lemma S3_place : ssPlace S3z = fun c : Fin 3 => ((c : ℕ) : ZMod 3) := by
  funext c
  simp only [ssPlace, S3z, map_add, constantCoeff_C, U3_const, add_zero]

/-- **`thm:S3`** (`t = 0`): the sequence is a `(0,3)`-sequence in base `3`. -/
theorem S3_net : IsSeq0 (zcode 3) S3gen := by
  refine ss_t0 (zcode 3) (fun _ => S3g) S3z ?_ (fun c => by rw [S3g_const]; exact one_ne_zero) ?_
  · rw [S3_place]
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)
  · intro c
    simp only [S3z, map_add, coeff_C, U3_coeff1]
    rw [if_neg (by norm_num), zero_add]; decide

/-- **`thm:S3`**: the sequence is a scramble `(L_0 P_0, L_1 P_1, L_2 P_2)` of the Faure sequence in
base `3` (`C_c = L_c P_c`, places `0, 1, 2`, `L_c[n][i] = [x^n] g U^i`). -/
theorem S3_faure : S3gen = scrGen (fun c : Fin 3 => ((c : ℕ) : ZMod 3)) (ssScr (fun _ => S3g) S3z) := by
  rw [← S3_place]; exact ss_eq_scr _ _

/-! ## Closed forms in the basis `{1, U, U²}` -/

lemma mk1_mul3' : (1 - X) * PowerSeries.mk (1 : ℕ → ZMod 3) = 1 := mk1_mul3

/-- **`thm:S3`, the frame matrix in closed form**: `(1 - x) M[c][b] = P_0 + P_1 U + P_2 U²` with the
numerators `S3Mn c b`. -/
theorem S3_M (c b : Fin 3) : (1 - X) * frameM (fun _ => S3g) S3z c b = tsemS (S3Mn c b) := by
  have hx := S3g_x
  have hU := U3_cube'
  have h3 := ps3_three
  have e : (1 - X) * frameM (fun _ => S3g) S3z c b = (1 + X + 2 * U3) * (C ((c : ℕ) : ZMod 3) + U3) ^ (b : ℕ) := by
    simp only [frameM, S3z]; rw [← sub3, ← hx]; ring
  rw [e, sub3] at *
  clear hx
  fin_cases c <;> fin_cases b <;>
    simp only [S3Mn00, S3Mn01, S3Mn02, S3Mn10, S3Mn11, S3Mn12, S3Mn20, S3Mn21, S3Mn22, tsemS, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, lps_cons, lps_nil, map_zero, map_one, map_ofNat, mul_zero, add_zero, zero_add,
      pow_zero, pow_one, pow_two, mul_one] <;>
    grind

/-- **`thm:S3`, `Ĝ` in closed form**: `x Q_p Ĝ[b][c'] = P_0 + P_1 U + P_2 U²` with the numerators
`S3An b c'`. -/
theorem S3_ghat (b c' : Fin 3) :
    X * lps QpS * (S3G b c' * PowerSeries.mk 1) = tsemS (S3An b c') := by
  have hx := S3g_x
  have hgi := S3g_inv
  have hU := U3_cube'
  have h3 := ps3_three
  have hm := mk1_mul3'
  rw [sub3, sub3] at hx
  rw [sub3] at hm
  fin_cases b <;> fin_cases c' <;>
    simp only [S3An00, S3An01, S3An02, S3An10, S3An11, S3An12, S3An20, S3An21, S3An22, S3G, S3Gp00, S3Gp01, S3Gp02, S3Gp10, S3Gp11, S3Gp12, S3Gp20, S3Gp21, S3Gp22, tsemS, QpS,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, lps_cons, lps_nil, map_zero, map_one, map_ofNat, mul_zero, add_zero,
      zero_add, pow_zero, pow_one, pow_two, mul_one] <;>
    (generalize S3g⁻¹ = gi at hgi ⊢; generalize S3g = g at hgi hx ⊢;
     generalize PowerSeries.mk (1 : ℕ → ZMod 3) = m at hm ⊢; grind)

/-! ## The initial states -/

lemma S3mtab_eq (c b : Fin 3) (a : ℕ) (ha : a < 8) :
    coeff a (frameM (fun _ => S3g) S3z c b) = S3mtab c b a := by
  have hm := mk1_mul3'
  have e : frameM (fun _ => S3g) S3z c b = tsemS (S3Mn c b) * PowerSeries.mk 1 := by
    rw [← S3_M]
    linear_combination (frameM (fun _ => S3g) S3z c b) * hm.symm
  have h1 : TRep 9 (List.replicate 9 (1 : ZMod 3)) (PowerSeries.mk 1) := fun n hn => by
    simp only [lget, coeff_mk, List.getD_eq_getElem?_getD, List.getElem?_replicate, hn, ite_true,
      Option.getD_some]; rfl
  rw [e, S3mtab, tmul_rep (tsemLS_rep 9 _) h1 a (by omega)]

lemma S3Mle_lps (i : ℕ) (hi : i < 8) (c b : Fin 3) :
    lps (S3Mle i c b) = ∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S3g) S3z c b)) * X ^ a := by
  rw [S3Mle, lps_range_map]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [S3mtab_eq c b a (by have := Finset.mem_range.mp ha; omega)]

lemma S3_dQ : lps ([0, 1, 0, 1] : List (ZMod 3)) = X * lps QpS * PowerSeries.mk 1 := by
  have hm := mk1_mul3'
  have h3 := ps3_three
  simp only [QpS, lps_cons, lps_nil, map_zero, map_one, map_ofNat, mul_zero, add_zero, zero_add,
    mul_one]
  rw [sub3] at hm
  generalize PowerSeries.mk (1 : ℕ → ZMod 3) = m at hm ⊢
  grind

/-- **The initial states** (`prop:automaton`, proof): `esemS (initSS i c c') = x^{8-i} F_i[c][c']`. -/
theorem esemS_init (i : ℕ) (hi : i < 8) (c c' : Fin 3) :
    esemS (initSS i c c') = X ^ (8 - i) * S3F i c c' := by
  have g0 := (S3_ghat 0 c').symm
  have g1 := (S3_ghat 1 c').symm
  have g2 := (S3_ghat 2 c').symm
  have hQ := QpS_unit
  have hdQ := S3_dQ
  have e8 : (X : PowerSeries (ZMod 3)) ^ (8 - i) = X ^ (7 - i) * X := by
    rw [← pow_succ]; congr 1; omega
  unfold esemS initSS S3F
  simp only [tsemS, initCS, lps_trim, lps_pshift, lps_padd, lps_pmul, lps_map_mul, S3Mle_lps i hi,
    Fin.sum_univ_three, e8, map_ofNat] at g0 g1 g2 ⊢
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S3g) S3z c 0)) * X ^ a) = S0
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S3g) S3z c 1)) * X ^ a) = S1
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S3g) S3z c 2)) * X ^ a) = S2
  generalize (X : PowerSeries (ZMod 3)) ^ (7 - i) = k
  generalize (lps QpS)⁻¹ = Qi at hQ ⊢
  by_cases hc : c = c'
  · simp only [hc, ite_true, lps_nil]
    linear_combination (k * Qi) * hdQ + (k * Qi * 2 * S0) * g0 + (k * Qi * 2 * S1) * g1 +
      (k * Qi * 2 * S2) * g2 +
      (k * X * (PowerSeries.mk 1 + 2 * (S0 * (S3G 0 c' * PowerSeries.mk 1) +
        S1 * (S3G 1 c' * PowerSeries.mk 1) + S2 * (S3G 2 c' * PowerSeries.mk 1)))) * hQ
  · simp only [hc, ite_false, lps_nil]
    linear_combination (k * Qi * 2 * S0) * g0 + (k * Qi * 2 * S1) * g1 + (k * Qi * 2 * S2) * g2 +
      (k * X * (2 * (S0 * (S3G 0 c' * PowerSeries.mk 1) +
        S1 * (S3G 1 c' * PowerSeries.mk 1) + S2 * (S3G 2 c' * PowerSeries.mk 1)))) * hQ

/-- **The initial states read the responses**: coefficient `l` of the initial state of entry
`(c, c')`, depth `i < 8`, is the carry response `D_i(l)[c][c']` of `prop:law`. -/
theorem S3_init (i : ℕ) (hi : i < 8) (c c' : Fin 3) (l : ℕ) :
    coeff (l + 8) (esemS (initSS i c c')) = lawD (fun _ => S3g) S3z S3G i l c c' := by
  rw [esemS_init i hi, coeff_X_pow_mul', if_pos (by omega), show l + 8 - (8 - i) = l + i by omega]
  unfold S3F lawD
  rw [map_add, show (2 : PowerSeries (ZMod 3)) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    map_sum, Finset.sum_comm]
  have hsum : ∀ b : Fin 3, coeff (l + i)
      ((∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S3g) S3z c b)) * X ^ a) *
        (S3G b c' * PowerSeries.mk 1)) =
      ∑ a ∈ range (i + 1), coeff a (frameM (fun _ => S3g) S3z c b) *
        coeff (l + i - a) (S3G b c' * PowerSeries.mk 1) := by
    intro b
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : a ≤ l + i := by have := Finset.mem_range.mp ha; omega
    rw [mul_assoc, coeff_C_mul, mul_comm (X ^ a), coeff_mul_X_pow', if_pos this]
  simp only [hsum]
  rw [Finset.sum_comm]
  have hδ : coeff (l + i) (if c = c' then PowerSeries.mk (1 : ℕ → ZMod 3) else 0) =
      if c = c' then 1 else 0 := by
    split_ifs <;> simp [coeff_mk]
  rw [hδ, zmod3_two_mul]

end GeoSeq
