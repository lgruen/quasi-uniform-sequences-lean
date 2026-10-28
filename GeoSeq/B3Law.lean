/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B3Auto
public import GeoSeq.Faure2
public import GeoSeq.FrameNets

@[expose] public section

/-!
# GeoSeq stage S6: the law of the base-3 sequence (`thm:B3`)

* `B3_roots`, `B3_frame_inv`, `B3_law`: `prop:law` applies (`w = z² - z`, `θ = 1`; the inverse frame
  matrix in the Faure form of `lem:gform`).
* `B3_net`: `t = 0` (`lem:t0` via `ss_t0`); `B3_faure`: `C_c = L_c P_{a_c}` with places `0, 1`.
* Closed forms in the basis `{1, τ^{-1}}` (`τ^{-1} = T3`, `lem:frames`(b)): the frame matrix
  `M = esem(B3Mn)` and `x² Q_p Ĝ = B3An` (`Ĝ = G/(1-x)`), proved by `grind` from `τ T3 = 1`,
  `τ² = 1 + x`, `3 = 0`.
* The initial states of `prop:automaton`: `esem (initS i c c') = x^{8-i} F_i[c][c']` with
  `[x^{l+i}] F_i[c][c'] = D_i(l)[c][c']`, so coefficient `l` of the state is the response
  (`B3_init`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Base-3 algebra (negation is rewritten as multiplication by `2`) -/

/-- In `𝔽_3[[x]]`, `-a = 2a` (used to remove unary negations, whose instance path is not seen by
`ring`/`grind`). -/
lemma neg3 (a : PowerSeries (ZMod 3)) : -a = 2 * a := by
  have h : a + 2 * a = 0 := by linear_combination a * ps3_three
  exact neg_eq_of_add_eq_zero_right h

lemma oneSubX_inv3 : (1 - X : PowerSeries (ZMod 3))⁻¹ = PowerSeries.mk 1 := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one
    (by rw [map_sub, map_one, constantCoeff_X]; exact one_ne_zero)]
  exact mk_one_mul_one_sub_eq_one (S := ZMod 3)

lemma mk1_mul3 : (1 - X) * PowerSeries.mk (1 : ℕ → ZMod 3) = 1 := by
  rw [mul_comm]; exact mk_one_mul_one_sub_eq_one (S := ZMod 3)

lemma B3g0_eq : B3g 0 = 2 * ((1 + X) * (1 - X + tau3)) * PowerSeries.mk 1 := by
  show -((1 + X) * (1 - X + tau3)) * (1 - X)⁻¹ = _
  rw [oneSubX_inv3, neg3]

lemma B3g1_eq : B3g 1 = 2 * (1 + T3) := by
  have h1 := tau3_T3
  have h3 := ps3_three
  show -(1 + tau3) * tau3⁻¹ = _
  rw [tau3_inv, neg3]
  grind

lemma B3_rho : B3z 1 - B3z 0 = tau3 := by
  show (2 - tau3) - (tau3 - 1) = tau3
  linear_combination (1 - tau3) * ps3_three

lemma B3z0_eq : B3z 0 = tau3 - 1 := rfl
lemma B3z1_eq : B3z 1 = 2 - tau3 := rfl

/-! ## The law -/

lemma B3_roots (c : Fin 2) :
    Polynomial.aeval (B3z c) (Polynomial.X ^ 2 + 2 * Polynomial.X : Polynomial (ZMod 3)) =
      PowerSeries.C (1 : ZMod 3) * X := by
  have h2 := tau3_sq
  have h3 := ps3_three
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_one, one_mul, map_ofNat]
  fin_cases c
  · show (tau3 - 1) ^ 2 + 2 * (tau3 - 1) = X
    linear_combination h2
  · show (2 - tau3) ^ 2 + 2 * (2 - tau3) = X
    linear_combination h2 + (3 - 2 * tau3) * h3

lemma B3_wdeg : (Polynomial.X ^ 2 + 2 * Polynomial.X : Polynomial (ZMod 3)).natDegree ≤ 2 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by rw [Polynomial.natDegree_X_pow])
      ((Polynomial.natDegree_mul_le).trans (by
        rw [Polynomial.natDegree_X]
        have : (2 : Polynomial (ZMod 3)).natDegree = 0 := Polynomial.natDegree_ofNat 2
        omega)))

lemma mk1_const3 : constantCoeff (PowerSeries.mk (1 : ℕ → ZMod 3)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; rfl

lemma B3g0_const : constantCoeff (B3g 0) = 1 := by
  rw [B3g0_eq, map_mul, map_mul, map_mul, map_add, map_add, map_sub, mk1_const3, tau3_const,
    constantCoeff_X, map_one, map_ofNat]
  decide

lemma B3g1_const : constantCoeff (B3g 1) = 1 := by
  rw [B3g1_eq, map_mul, map_add, T3_const, map_one, map_ofNat]
  decide

lemma B3g_const (c : Fin 2) : constantCoeff (B3g c) = 1 := by
  fin_cases c
  · exact B3g0_const
  · exact B3g1_const

lemma B3k_spec (c : Fin 2) : B3k c * ((B3z 1 - B3z 0) * B3g c) = 1 := by
  apply PowerSeries.inv_mul_cancel
  rw [B3_rho, map_mul, tau3_const, B3g_const]; exact one_ne_zero

/-- **`thm:B3`**: `M G = 1` for the frame matrix `M = ((g_0, g_0 z_0), (g_1, g_1 z_1))` and
`G = B3G` (the Faure form of `lem:gform`). -/
theorem B3_frame_inv : frameM B3g B3z * B3G = 1 := by
  show frameM ![B3g 0, B3g 1] ![B3z 0, B3z 1] * faureG (B3z 0) (B3z 1) (B3k 0) (B3k 1) = 1
  exact faure_inv _ _ _ _ _ _ (B3k_spec 0) (B3k_spec 1)

/-- **`thm:B3`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the base-3 sequence is `lawD B3g B3z B3G i l c c'` (independent of `K`). -/
theorem B3_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 2) :
    IsCarryEntry B3gen K i l c c' (lawD B3g B3z B3G i l c c') :=
  law B3g B3z _ B3_wdeg 1 1 (one_mul 1) B3_roots B3G B3_frame_inv K i l hl hlK c c'

/-! ## `t = 0` and the Faure form -/

lemma B3_place : ssPlace B3z = ![0, 1] := by
  funext c
  fin_cases c
  · show constantCoeff (tau3 - 1) = 0
    rw [map_sub, tau3_const, map_one]; decide
  · show constantCoeff (2 - tau3) = 1
    rw [map_sub, tau3_const, map_ofNat]; decide

lemma tau3_coeff1 : coeff 1 tau3 = 2 := by
  rw [tau3, rhoWF_coeff1, one_mul]
  exact (eq_inv_of_mul_eq_one_left (by decide : (2 : ZMod 3) * 2 = 1)).symm

/-- **`thm:B3`** (`t = 0`): the base-3 sequence is a `(0,2)`-sequence. -/
theorem B3_net : IsSeq0 (zcode 3) B3gen := by
  refine ss_t0 (zcode 3) B3g B3z ?_ (fun c => by rw [B3g_const]; exact one_ne_zero) ?_
  · rw [B3_place]
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  · intro c
    fin_cases c
    · show coeff 1 (tau3 - 1) ≠ 0
      rw [map_sub, tau3_coeff1, coeff_one]; decide
    · show coeff 1 (2 - tau3) ≠ 0
      rw [map_sub, tau3_coeff1, show (2 : PowerSeries (ZMod 3)) = C 2 from (map_ofNat C 2).symm,
        coeff_C]; decide

/-- **`thm:B3`**: the sequence is a scramble `(L_0 P_0, L_1 P_1)` of the Faure sequence in base `3`
(`C_c = L_c P_{a_c}`, places `a_0 = 0`, `a_1 = 1`, `L_c[n][i] = [x^n] g_c (z_c - a_c)^i`). -/
theorem B3_faure : B3gen = scrGen ![0, 1] (ssScr B3g B3z) := by
  rw [← B3_place]; exact ss_eq_scr B3g B3z

/-! ## Closed forms in the basis `{1, τ^{-1}}` -/

lemma B3G00 : B3G 0 0 = (2 - tau3) * B3k 0 := rfl
lemma B3G01 : B3G 0 1 = -((tau3 - 1) * B3k 1) := rfl
lemma B3G10 : B3G 1 0 = -(B3k 0) := rfl
lemma B3G11 : B3G 1 1 = B3k 1 := rfl

lemma B3k0_spec : B3k 0 * (tau3 * (2 * ((1 + X) * (1 - X + tau3)) * PowerSeries.mk 1)) = 1 := by
  have h := B3k_spec 0
  rwa [B3_rho, B3g0_eq] at h

lemma B3k1_spec : B3k 1 * (tau3 * (2 * (1 + T3))) = 1 := by
  have h := B3k_spec 1
  rwa [B3_rho, B3g1_eq] at h

/-- **`thm:B3`, `Ĝ` in closed form**: `x² Q_p Ĝ[b][c'] = A + B τ^{-1}` with the numerators `B3An`. -/
theorem B3_ghat (b c' : Fin 2) :
    lps (B3An b c').1 + lps (B3An b c').2 * T3 = X ^ 2 * lps Qp3 * (B3G b c' * PowerSeries.mk 1) := by
  have h1 := tau3_T3
  have h2 := tau3_sq
  have h3 := ps3_three
  have hm := mk1_mul3
  have hk0 := B3k0_spec
  have hk1 := B3k1_spec
  fin_cases b <;> fin_cases c' <;>
    simp only [B3An, Qp3, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, B3G00, B3G01, B3G10, B3G11, neg3, lps_cons, lps_nil, map_zero, map_one,
      map_ofNat, mul_zero, add_zero, zero_add] <;>
    grind

/-- **`thm:B3`, the frame matrix in closed form**: `M[c][b] = (P_0 + P_1 τ^{-1})/Q_p` with the
numerators `B3Mn`. -/
theorem B3_M (c b : Fin 2) : frameM B3g B3z c b = esem (B3Mn c b) := by
  have h1 := tau3_T3
  have h2 := tau3_sq
  have h3 := ps3_three
  have hm := mk1_mul3
  have hτ := tau3_eq
  have key : frameM B3g B3z c b * lps Qp3 = lps (B3Mn c b).1 + lps (B3Mn c b).2 * T3 := by
    fin_cases c <;> fin_cases b <;>
      simp only [frameM, B3Mn, Qp3, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, B3g0_eq,
        B3g1_eq, B3z0_eq, B3z1_eq, lps_cons, lps_nil, map_zero, map_one, map_ofNat, mul_zero,
        add_zero, zero_add] <;>
      grind
  rw [esem, ← key, mul_assoc, Qp3_unit, mul_one]

lemma B3mtab_eq (c b : Fin 2) (a : ℕ) (ha : a < 6) :
    coeff a (frameM B3g B3z c b) = B3mtab c b a := by
  rw [B3_M, B3mtab, acoefN_eq 6 _ a ha]

/-! ## The initial states -/

lemma lps_range_map {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    lps ((List.range n).map f) = ∑ a ∈ range n, C (f a) * X ^ a := by
  ext k
  rw [map_sum]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_range, lps, coeff_mk, lget]
  by_cases hk : k < n
  · simp [hk, List.getD_eq_getElem?_getD]
  · simp [hk, List.getD_eq_getElem?_getD]

lemma B3Mle_lps (i : ℕ) (hi : i < 6) (c b : Fin 2) :
    lps (B3Mle i c b) = ∑ a ∈ range (i + 1), C (coeff a (frameM B3g B3z c b)) * X ^ a := by
  rw [B3Mle, lps_range_map]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [B3mtab_eq c b a (by have := Finset.mem_range.mp ha; omega)]

lemma B3_dQ : lps ([0, 0, 2, 2] : List (ZMod 3)) = X ^ 2 * lps Qp3 * PowerSeries.mk 1 := by
  have h3 := ps3_three
  have hm := mk1_mul3
  simp only [Qp3, lps_cons, lps_nil, map_zero, map_ofNat, mul_zero, add_zero, zero_add]
  grind

/-- **The initial states** (`prop:automaton`, proof): `esem (initS i c c') = x^{8-i} F_i[c][c']`. -/
theorem esem_init (i : ℕ) (hi : i < 6) (c c' : Fin 2) :
    esem (initS i c c') = X ^ (8 - i) * B3F i c c' := by
  have g0 := B3_ghat 0 c'
  have g1 := B3_ghat 1 c'
  have hQ := Qp3_unit
  have hdQ := B3_dQ
  have e8 : (X : PowerSeries (ZMod 3)) ^ (8 - i) = X ^ (6 - i) * X ^ 2 := by
    rw [← pow_add]; congr 1; omega
  unfold esem initS B3F
  simp only [lps_trim, lps_pshift, lps_padd, lps_map_mul, lps_pmul, B3Mle_lps i hi, map_ofNat,
    Fin.sum_univ_two, e8]
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM B3g B3z c 0)) * X ^ a) = S0
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM B3g B3z c 1)) * X ^ a) = S1
  generalize (X : PowerSeries (ZMod 3)) ^ (6 - i) = k
  generalize (lps Qp3)⁻¹ = Qi at hQ ⊢
  by_cases hc : c = c'
  · simp only [hc, ite_true]
    linear_combination (k * Qi) * hdQ + (k * Qi * 2 * S0) * g0 + (k * Qi * 2 * S1) * g1 +
      (k * X ^ 2 * (PowerSeries.mk 1 + 2 * (S0 * (B3G 0 c' * PowerSeries.mk 1) +
        S1 * (B3G 1 c' * PowerSeries.mk 1)))) * hQ
  · simp only [hc, ite_false, lps_nil]
    linear_combination (k * Qi * 2 * S0) * g0 + (k * Qi * 2 * S1) * g1 +
      (k * X ^ 2 * (2 * (S0 * (B3G 0 c' * PowerSeries.mk 1) +
        S1 * (B3G 1 c' * PowerSeries.mk 1)))) * hQ

lemma zmod3_two_mul (x y : ZMod 3) : x + 2 * y = x - y := by
  revert x y; decide

/-- **The initial states read the responses**: coefficient `l` of the initial state of entry
`(c, c')`, depth `i < 6`, is the carry response `D_i(l)[c][c']` of `prop:law`. -/
theorem B3_init (i : ℕ) (hi : i < 6) (c c' : Fin 2) (l : ℕ) :
    coeff (l + 8) (esem (initS i c c')) = lawD B3g B3z B3G i l c c' := by
  rw [esem_init i hi, coeff_X_pow_mul', if_pos (by omega), show l + 8 - (8 - i) = l + i by omega]
  unfold B3F lawD
  rw [map_add, show (2 : PowerSeries (ZMod 3)) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    map_sum, Finset.sum_comm]
  have hsum : ∀ b : Fin 2, coeff (l + i)
      ((∑ a ∈ range (i + 1), C (coeff a (frameM B3g B3z c b)) * X ^ a) * (B3G b c' * PowerSeries.mk 1)) =
      ∑ a ∈ range (i + 1), coeff a (frameM B3g B3z c b) *
        coeff (l + i - a) (B3G b c' * PowerSeries.mk 1) := by
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
