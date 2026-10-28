/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S4Auto
public import GeoSeq.K4Law
public import GeoSeq.S4SymDefs

@[expose] public section

/-!
# GeoSeq stage S8: the law of the Artin–Schreier sequence over `𝔽_4` (`thm:S4`)

* `S4_roots`, `S4_frame_inv`, `S4_law`: `prop:law` applies (`w = z⁴ + z`, `θ = 1`;
  `G = T^{-1} A^{-1} g^{-1}`).
* `S4_net`: `t = 0` (`lem:t0` via `ss_t0`; places `0, 1, ω, ω²`, `g(0) = 1`, `[x] z_c = 1`).
* Closed forms in the basis `{1, U, U², U³}` (`U⁴ = U + x`): `M[c][b] = S4Mn c b` (`S4_M`), the norm
  `g · (ω² + ωx + (ω² + ωx)U + (ω + x)U²) = ω² + x²` (`S4_norm`), `Q_p Ĝ[b][c'] = S4An b c'` (`S4_ghat`).
* The initial states: `esemU (initSU i c c' sh) = x^{5-i+sh} F_i[c][c']` (`esemU_init`, `S4_init`,
  `S4_init1`).
-/

namespace GeoSeq

open Finset PowerSeries

lemma S4GpN00 : S4GpN 0 0 = ([.e1], [], [], [.e1]) := rfl
lemma S4GpN01 : S4GpN 0 1 = ([], [.e1], [.e1], [.e1]) := rfl
lemma S4GpN02 : S4GpN 0 2 = ([], [.ew2], [.ew], [.e1]) := rfl
lemma S4GpN03 : S4GpN 0 3 = ([], [.ew], [.ew2], [.e1]) := rfl
lemma S4GpN10 : S4GpN 1 0 = ([], [], [.e1], []) := rfl
lemma S4GpN11 : S4GpN 1 1 = ([.e1], [], [.e1], []) := rfl
lemma S4GpN12 : S4GpN 1 2 = ([.ew2], [], [.e1], []) := rfl
lemma S4GpN13 : S4GpN 1 3 = ([.ew], [], [.e1], []) := rfl
lemma S4GpN20 : S4GpN 2 0 = ([], [.e1], [], []) := rfl
lemma S4GpN21 : S4GpN 2 1 = ([.e1], [.e1], [], []) := rfl
lemma S4GpN22 : S4GpN 2 2 = ([.ew], [.e1], [], []) := rfl
lemma S4GpN23 : S4GpN 2 3 = ([.ew2], [.e1], [], []) := rfl
lemma S4GpN30 : S4GpN 3 0 = ([.e1], [], [], []) := rfl
lemma S4GpN31 : S4GpN 3 1 = ([.e1], [], [], []) := rfl
lemma S4GpN32 : S4GpN 3 2 = ([.e1], [], [], []) := rfl
lemma S4GpN33 : S4GpN 3 3 = ([.e1], [], [], []) := rfl
lemma S4Mn00 : S4Mn 0 0 = ([.e1], [.ew], [.e1], []) := rfl
lemma S4Mn01 : S4Mn 0 1 = ([], [.e1], [.ew], [.e1]) := rfl
lemma S4Mn02 : S4Mn 0 2 = ([.e0, .e1], [.e1], [.e1], [.ew]) := rfl
lemma S4Mn03 : S4Mn 0 3 = ([.e0, .ew], [.ew, .e1], [.e1], [.e1]) := rfl
lemma S4Mn10 : S4Mn 1 0 = ([.e1], [.ew], [.e1], []) := rfl
lemma S4Mn11 : S4Mn 1 1 = ([.e1], [.ew2], [.ew2], [.e1]) := rfl
lemma S4Mn12 : S4Mn 1 2 = ([.e1, .e1], [.ew2], [], [.ew]) := rfl
lemma S4Mn13 : S4Mn 1 3 = ([.e1, .ew2], [.e0, .e1], [.ew2], [.ew]) := rfl
lemma S4Mn20 : S4Mn 2 0 = ([.e1], [.ew], [.e1], []) := rfl
lemma S4Mn21 : S4Mn 2 1 = ([.ew], [.ew], [], [.e1]) := rfl
lemma S4Mn22 : S4Mn 2 2 = ([.ew2, .e1], [], [.ew], [.ew]) := rfl
lemma S4Mn23 : S4Mn 2 3 = ([.e1], [.e1, .e1], [.ew2], [.e1]) := rfl
lemma S4Mn30 : S4Mn 3 0 = ([.e1], [.ew], [.e1], []) := rfl
lemma S4Mn31 : S4Mn 3 1 = ([.ew2], [], [.e1], [.e1]) := rfl
lemma S4Mn32 : S4Mn 3 2 = ([.ew, .e1], [.ew], [.ew2], [.ew]) := rfl
lemma S4Mn33 : S4Mn 3 3 = ([.e1, .e1], [.e1, .e1], [], [.ew]) := rfl
lemma S4An00 : S4An 0 0 = ([.ew2, .e1, .ew], [.e0, .ew, .e1], [], [.ew2, .ew]) := rfl
lemma S4An01 : S4An 0 1 = ([.e0, .e1, .ew2], [.ew, .ew2, .e1], [.ew, .e1], [.ew, .e1]) := rfl
lemma S4An02 : S4An 0 2 = ([], [.ew, .ew2, .e1], [.e1, .ew2], [.ew2, .ew]) := rfl
lemma S4An03 : S4An 0 3 = ([.e0, .ew, .e1], [.ew2, .e0, .e1], [.e1, .ew2], [.ew, .e1]) := rfl
lemma S4An10 : S4An 1 0 = ([.e0, .ew, .e1], [.ew, .e1], [.ew2, .ew], [.ew2, .ew]) := rfl
lemma S4An11 : S4An 1 1 = ([.ew2, .e0, .e1], [.e1, .ew2], [.e1, .ew2], [.ew2, .ew]) := rfl
lemma S4An12 : S4An 1 2 = ([.ew, .ew2, .e1], [], [.ew, .e1], [.ew2, .ew]) := rfl
lemma S4An13 : S4An 1 3 = ([.e1, .e1, .e1], [.ew2, .ew], [], [.ew2, .ew]) := rfl
lemma S4An20 : S4An 2 0 = ([], [.ew2, .ew], [.ew2, .ew], [.ew, .e1]) := rfl
lemma S4An21 : S4An 2 1 = ([.ew2, .ew], [], [.e1, .ew2], [.ew, .e1]) := rfl
lemma S4An22 : S4An 2 2 = ([.e1, .ew2], [.ew, .e1], [], [.ew, .e1]) := rfl
lemma S4An23 : S4An 2 3 = ([.ew, .e1], [.e1, .ew2], [.ew, .e1], [.ew, .e1]) := rfl
lemma S4An30 : S4An 3 0 = ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []) := rfl
lemma S4An31 : S4An 3 1 = ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []) := rfl
lemma S4An32 : S4An 3 2 = ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []) := rfl
lemma S4An33 : S4An 3 3 = ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []) := rfl

lemma fin4_val3 : ((3 : Fin 4) : ℕ) = 3 := rfl

/-! ## The multiplier and the law -/

lemma S4g_const : constantCoeff S4g = 1 := by
  unfold S4g
  rw [map_add, map_add, map_mul, map_pow, U4_const, constantCoeff_C, map_one]; rfl

lemma S4g_inv : S4g * S4g⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [S4g_const]; exact one_ne_zero)

lemma S4a_quart (c : Fin 4) : (C (S4a c) : PowerSeries F4) ^ 4 = C (S4a c) := by
  rw [← map_pow]; congr 1; fin_cases c <;> rfl

/-- `w = z⁴ + z` over `𝔽_4`. -/
lemma S4_roots (c : Fin 4) :
    Polynomial.aeval (S4z c) (Polynomial.X ^ 4 + Polynomial.X : Polynomial F4) =
      PowerSeries.C (1 : F4) * X := by
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one, one_mul, S4z]
  have ha := S4a_quart c
  linear_combination ha + U4_quart + (C (S4a c) + 2 * C (S4a c) ^ 3 * U4 + 3 * C (S4a c) ^ 2 * U4 ^ 2 +
    2 * C (S4a c) * U4 ^ 3) * ps4_two

lemma S4_wdeg : (Polynomial.X ^ 4 + Polynomial.X : Polynomial F4).natDegree ≤ 4 :=
  (Polynomial.natDegree_add_le _ _).trans (max_le (by rw [Polynomial.natDegree_X_pow])
    (by rw [Polynomial.natDegree_X]; norm_num))

lemma S4a_vals : S4a 0 = 0 ∧ S4a 1 = 1 ∧ S4a 2 = F4.w ∧ S4a 3 = F4.w2 := ⟨rfl, rfl, rfl, rfl⟩

/-- **`thm:S4`**: `M G = 1` for the frame matrix `M[c][b] = g (a_c + U)^b` and `G = S4G`. -/
theorem S4_frame_inv : frameM (fun _ => S4g) S4z * S4G = 1 := by
  have hgi := S4g_inv
  have h2 := ps4_two
  have hw := C_ew_sq
  ext1 c c'
  rw [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
  fin_cases c <;> fin_cases c' <;>
    simp only [frameM, S4z, S4G, S4a, f4dec, S4GpN00, S4GpN01, S4GpN02, S4GpN03, S4GpN10, S4GpN11, S4GpN12, S4GpN13, S4GpN20, S4GpN21, S4GpN22, S4GpN23, S4GpN30, S4GpN31, S4GpN32, S4GpN33, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two, tsemU, lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1, C_ew2, map_one, map_zero, mul_zero, add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ite_true, ite_false,
      Fin.reduceEq, fin4_val3, Nat.reduceAdd] <;>
    (generalize S4g⁻¹ = gi at hgi ⊢; generalize S4g = g at hgi ⊢; grind)

/-- **`thm:S4`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the sequence is `lawD (fun _ => g) z G i l c c'` (independent of `K`). -/
theorem S4_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 4) :
    IsCarryEntry S4gen K i l c c' (lawD (fun _ => S4g) S4z S4G i l c c') :=
  law (fun _ => S4g) S4z _ S4_wdeg 1 1 (one_mul 1) S4_roots S4G S4_frame_inv K i l hl hlK c c'

/-! ## `t = 0` -/

lemma S4_place : ssPlace S4z = S4a := by
  funext c
  simp only [ssPlace, S4z, map_add, constantCoeff_C, U4_const, add_zero]

/-- **`thm:S4`** (`t = 0`): the sequence is a `(0,4)`-sequence in base `4`. -/
theorem S4_net : IsSeq0 f4code S4gen := by
  refine ss_t0 f4code (fun _ => S4g) S4z ?_ (fun c => by rw [S4g_const]; exact one_ne_zero) ?_
  · rw [S4_place]
    intro a b h
    revert a b; decide
  · intro c
    simp only [S4z, map_add, coeff_C, U4_coeff1, if_neg (show (1 : ℕ) ≠ 0 by norm_num), zero_add]
    exact one_ne_zero

/-! ## Closed forms in the basis `{1, U, U², U³}` -/

/-- `U⁴ = U + x` without powers (for `grind`). -/
lemma U4_quart' : U4 * (U4 * (U4 * U4)) = U4 + X := by
  linear_combination U4_quart - U4 * ps4_two

/-- **`thm:S4`, the frame matrix in closed form**: `M[c][b] = ∑_k P_k U^k` with the numerators
`S4Mn c b`. -/
theorem S4_M (c b : Fin 4) : frameM (fun _ => S4g) S4z c b = tsemU (S4Mn c b) := by
  have hU := U4_quart'
  have h2 := ps4_two
  have hw := C_ew_sq
  fin_cases c <;> fin_cases b <;>
    simp only [frameM, S4z, S4g, S4a, f4dec, S4Mn00, S4Mn01, S4Mn02, S4Mn03, S4Mn10, S4Mn11, S4Mn12, S4Mn13, S4Mn20, S4Mn21, S4Mn22, S4Mn23, S4Mn30, S4Mn31, S4Mn32, S4Mn33, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two, tsemU, lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1, C_ew2, map_one, map_zero, mul_zero, add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul, pow_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, fin4_val3, pow_succ] <;>
    grind

/-- The cofactor of the norm of `g`: `g^{-1} = (ω² + ωx + (ω² + ωx)U + (ω + x)U²)/(ω² + x²)`. -/
def S4prodN : StU := ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], [])

/-- **The norm of `g`**: `g · (ω² + ωx + (ω² + ωx)U + (ω + x)U²) = ω² + x²`. -/
theorem S4_norm : S4g * tsemU S4prodN = C F4.w2 + X ^ 2 := by
  have hU := U4_quart'
  have h2 := ps4_two
  have hw := C_ew_sq
  simp only [S4g, S4prodN, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two, tsemU, lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1, C_ew2, map_one, map_zero, mul_zero, add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul, pow_two, pow_succ]
  grind

lemma S4_ginvN : S4g⁻¹ * (C F4.w2 + X ^ 2) = tsemU S4prodN := by
  have hn := S4_norm
  have hgi := S4g_inv
  linear_combination (S4g⁻¹) * hn.symm + (tsemU S4prodN) * hgi

lemma lps_QpU : lps QpU = (C F4.w2 + X ^ 2) * (1 + X) := by
  simp only [QpU, lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1, map_one, map_zero, mul_zero, add_zero]
  ring

/-- The polynomial identities `T^{-1} A^{-1} · (cofactor of the norm) = S4An` (mod `U⁴ = U + x`). -/
lemma S4_gp_prod (b c' : Fin 4) : tsemU (S4GpN b c') * tsemU S4prodN = tsemU (S4An b c') := by
  have hU := U4_quart'
  have h2 := ps4_two
  have hw := C_ew_sq
  fin_cases b <;> fin_cases c' <;>
    simp only [S4prodN, S4GpN00, S4GpN01, S4GpN02, S4GpN03, S4GpN10, S4GpN11, S4GpN12, S4GpN13, S4GpN20, S4GpN21, S4GpN22, S4GpN23, S4GpN30, S4GpN31, S4GpN32, S4GpN33, S4An00, S4An01, S4An02, S4An03, S4An10, S4An11, S4An12, S4An13, S4An20, S4An21, S4An22, S4An23, S4An30, S4An31, S4An32, S4An33, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two, tsemU, lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1, C_ew2, map_one, map_zero, mul_zero, add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul, pow_two, pow_succ] <;>
    grind

/-- **`thm:S4`, `Ĝ` in closed form**: `Q_p Ĝ[b][c'] = ∑_k P_k U^k` with the numerators `S4An b c'`. -/
theorem S4_ghat (b c' : Fin 4) :
    lps QpU * (S4G b c' * PowerSeries.mk 1) = tsemU (S4An b c') := by
  have hm := mk1_mul4
  have hN := S4_ginvN
  rw [← S4_gp_prod, lps_QpU]
  simp only [S4G]
  linear_combination (tsemU (S4GpN b c') * (1 + X) * PowerSeries.mk 1) * hN +
    (tsemU (S4GpN b c') * tsemU S4prodN) * hm

/-! ## The initial states -/

lemma S4mtab_eq (c b : Fin 4) (a : ℕ) (ha : a < 5) :
    coeff a (frameM (fun _ => S4g) S4z c b) = S4mtab c b a := by
  rw [S4_M, S4mtab, tsemLU_rep _ a (by omega)]

lemma S4Mle_lps (i : ℕ) (hi : i < 5) (c b : Fin 4) :
    lps (S4Mle i c b) = ∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c b)) * X ^ a := by
  rw [S4Mle, lps_range_map]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [S4mtab_eq c b a (by have := Finset.mem_range.mp ha; omega)]

lemma S4_dQ : lps ([.ew2, .e0, .e1] : List F4) = lps QpU * PowerSeries.mk 1 := by
  have hm := mk1_mul4
  rw [lps_QpU]
  simp only [lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1, map_one, map_zero, mul_zero, add_zero, zero_add]
  linear_combination (-(C F4.ew2 + X ^ 2)) * hm

/-- **The initial states** (`prop:automaton`, proof): `esemU (initSU i c c' sh) = x^{5-i+sh} F_i[c][c']`. -/
theorem esemU_init (i : ℕ) (hi : i < 5) (c c' : Fin 4) (sh : ℕ) :
    esemU (initSU i c c' sh) = X ^ (5 - i + sh) * S4F i c c' := by
  have g0 := S4_ghat 0 c'
  have g1 := S4_ghat 1 c'
  have g2 := S4_ghat 2 c'
  have g3 := S4_ghat 3 c'
  have hQ := QpU_unit
  have hdQ := S4_dQ
  unfold esemU initSU S4F
  simp only [tsemU, initCU, lps_trim, lps_pshift, lps_padd, lps_pmul, S4Mle_lps i hi, Fin.sum_univ_four]
    at g0 g1 g2 g3 ⊢
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c 0)) * X ^ a) = S0
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c 1)) * X ^ a) = S1
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c 2)) * X ^ a) = S2
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c 3)) * X ^ a) = S3
  generalize (X : PowerSeries F4) ^ (5 - i + sh) = k
  generalize (lps QpU)⁻¹ = Qi at hQ ⊢
  by_cases hc : c = c'
  · simp only [hc, ite_true, lps_nil]
    linear_combination (k * Qi) * hdQ - (k * Qi * S0) * g0 - (k * Qi * S1) * g1 - (k * Qi * S2) * g2 -
      (k * Qi * S3) * g3 +
      (k * (PowerSeries.mk 1 + (S0 * (S4G 0 c' * PowerSeries.mk 1) + S1 * (S4G 1 c' * PowerSeries.mk 1) +
        S2 * (S4G 2 c' * PowerSeries.mk 1) + S3 * (S4G 3 c' * PowerSeries.mk 1)))) * hQ
  · simp only [hc, ite_false, lps_nil]
    linear_combination - (k * Qi * S0) * g0 - (k * Qi * S1) * g1 - (k * Qi * S2) * g2 -
      (k * Qi * S3) * g3 +
      (k * ((S0 * (S4G 0 c' * PowerSeries.mk 1) + S1 * (S4G 1 c' * PowerSeries.mk 1) +
        S2 * (S4G 2 c' * PowerSeries.mk 1) + S3 * (S4G 3 c' * PowerSeries.mk 1)))) * hQ

/-- Coefficient `n + i` of `F_i[c][c']` is the response `D_i(n)[c][c']` of `prop:law`. -/
theorem S4F_coeff (i : ℕ) (c c' : Fin 4) (n : ℕ) :
    coeff (n + i) (S4F i c c') = lawD (fun _ => S4g) S4z S4G i n c c' := by
  unfold S4F lawD
  rw [map_add, map_sum]
  have hsum : ∀ b : Fin 4, coeff (n + i)
      ((∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c b)) * X ^ a) *
        (S4G b c' * PowerSeries.mk 1)) =
      ∑ a ∈ range (i + 1), coeff a (frameM (fun _ => S4g) S4z c b) *
        coeff (n + i - a) (S4G b c' * PowerSeries.mk 1) := by
    intro b
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : a ≤ n + i := by have := Finset.mem_range.mp ha; omega
    rw [mul_assoc, coeff_C_mul, mul_comm (X ^ a), coeff_mul_X_pow', if_pos this]
  simp only [hsum]
  rw [Finset.sum_comm]
  have hδ : coeff (n + i) (if c = c' then PowerSeries.mk (1 : ℕ → F4) else 0) =
      if c = c' then 1 else 0 := by
    split_ifs <;> simp [coeff_mk]
  rw [hδ, f4_sub]

/-- Coefficient `l` of `initSU i c c' 0` is `D_i(l)[c][c']`. -/
theorem S4_init (i : ℕ) (hi : i < 5) (c c' : Fin 4) (l : ℕ) :
    coeff (l + 5) (esemU (initSU i c c' 0)) = lawD (fun _ => S4g) S4z S4G i l c c' := by
  rw [esemU_init i hi c c' 0, coeff_X_pow_mul', if_pos (by omega),
    show l + 5 - (5 - i + 0) = l + i by omega, S4F_coeff]

/-- Coefficient `l ≥ 1` of `initSU i c c' 1` is `D_i(l-1)[c][c']`. -/
theorem S4_init1 (i : ℕ) (hi : i < 5) (c c' : Fin 4) (l : ℕ) (hl : 1 ≤ l) :
    coeff (l + 5) (esemU (initSU i c c' 1)) = lawD (fun _ => S4g) S4z S4G i (l - 1) c c' := by
  rw [esemU_init i hi c c' 1, coeff_X_pow_mul', if_pos (by omega),
    show l + 5 - (5 - i + 1) = (l - 1) + i by omega, S4F_coeff]

/-! ## Translation symmetry (`H = 𝔽_4` acts on the places) -/

lemma sum_conj {s : ℕ} {R : Type*} [CommRing R] (P : Fin s → Fin s → R) (m γ : Fin s → R)
    (hP : ∀ b' b'', ∑ b, P b' b * P b b'' = if b' = b'' then 1 else 0) :
    ∑ b, (∑ b', P b' b * m b') * (∑ b'', P b b'' * γ b'') = ∑ b', m b' * γ b' := by
  have e : ∀ b, (∑ b', P b' b * m b') * (∑ b'', P b b'' * γ b'') =
      ∑ b', ∑ b'', m b' * γ b'' * (P b' b * P b b'') := by
    intro b; rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b'' _ => ?_
    ring
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hP, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Conjugation invariance of the law** (any frame): if permuting the rows of the frame matrix by `σ`
is right multiplication by a constant matrix `P`, permuting the columns of `G` by `σ` is left
multiplication by `P`, and `P² = I`, then `D_i(l)[σc][σc'] = D_i(l)[c][c']`. -/
theorem lawD_conj {s : ℕ} {R : Type*} [CommRing R] (g zθ : Fin s → PowerSeries R)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (σ : Fin s → Fin s) (P : Fin s → Fin s → R)
    (hM : ∀ c b, frameM g zθ (σ c) b = ∑ b', C (P b' b) * frameM g zθ c b')
    (hG : ∀ b c', G b (σ c') = ∑ b'', C (P b b'') * G b'' c')
    (hP : ∀ b' b'', ∑ b, P b' b * P b b'' = if b' = b'' then 1 else 0)
    (hσ : ∀ c c', σ c = σ c' ↔ c = c') (i l : ℕ) (c c' : Fin s) :
    lawD g zθ G i l (σ c) (σ c') = lawD g zθ G i l c c' := by
  unfold lawD
  have hδ : (if σ c = σ c' then (1 : R) else 0) = if c = c' then 1 else 0 := by
    by_cases h : c = c'
    · rw [if_pos ((hσ c c').mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hσ c c').mp h')), if_neg h]
  rw [hδ]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : ∀ b, coeff a (frameM g zθ (σ c) b) = ∑ b', P b' b * coeff a (frameM g zθ c b') := by
    intro b; rw [hM, map_sum]; simp only [coeff_C_mul]
  have e2 : ∀ b, coeff (l + i - a) (G b (σ c') * PowerSeries.mk 1) =
      ∑ b'', P b b'' * coeff (l + i - a) (G b'' c' * PowerSeries.mk 1) := by
    intro b; rw [hG, Finset.sum_mul, map_sum]; simp only [mul_assoc, coeff_C_mul]
  simp only [e1, e2]
  exact sum_conj P _ _ hP

lemma S4P000 : S4P 0 0 0 = 1 := by decide
lemma S4P001 : S4P 0 0 1 = 0 := by decide
lemma S4P002 : S4P 0 0 2 = 0 := by decide
lemma S4P003 : S4P 0 0 3 = 0 := by decide
lemma S4P010 : S4P 0 1 0 = 0 := by decide
lemma S4P011 : S4P 0 1 1 = 1 := by decide
lemma S4P012 : S4P 0 1 2 = 0 := by decide
lemma S4P013 : S4P 0 1 3 = 0 := by decide
lemma S4P020 : S4P 0 2 0 = 0 := by decide
lemma S4P021 : S4P 0 2 1 = 0 := by decide
lemma S4P022 : S4P 0 2 2 = 1 := by decide
lemma S4P023 : S4P 0 2 3 = 0 := by decide
lemma S4P030 : S4P 0 3 0 = 0 := by decide
lemma S4P031 : S4P 0 3 1 = 0 := by decide
lemma S4P032 : S4P 0 3 2 = 0 := by decide
lemma S4P033 : S4P 0 3 3 = 1 := by decide
lemma S4P100 : S4P 1 0 0 = 1 := by decide
lemma S4P101 : S4P 1 0 1 = 1 := by decide
lemma S4P102 : S4P 1 0 2 = 1 := by decide
lemma S4P103 : S4P 1 0 3 = 1 := by decide
lemma S4P110 : S4P 1 1 0 = 0 := by decide
lemma S4P111 : S4P 1 1 1 = 1 := by decide
lemma S4P112 : S4P 1 1 2 = 0 := by decide
lemma S4P113 : S4P 1 1 3 = 1 := by decide
lemma S4P120 : S4P 1 2 0 = 0 := by decide
lemma S4P121 : S4P 1 2 1 = 0 := by decide
lemma S4P122 : S4P 1 2 2 = 1 := by decide
lemma S4P123 : S4P 1 2 3 = 1 := by decide
lemma S4P130 : S4P 1 3 0 = 0 := by decide
lemma S4P131 : S4P 1 3 1 = 0 := by decide
lemma S4P132 : S4P 1 3 2 = 0 := by decide
lemma S4P133 : S4P 1 3 3 = 1 := by decide
lemma S4P200 : S4P 2 0 0 = 1 := by decide
lemma S4P201 : S4P 2 0 1 = F4.ew := by decide
lemma S4P202 : S4P 2 0 2 = F4.ew2 := by decide
lemma S4P203 : S4P 2 0 3 = 1 := by decide
lemma S4P210 : S4P 2 1 0 = 0 := by decide
lemma S4P211 : S4P 2 1 1 = 1 := by decide
lemma S4P212 : S4P 2 1 2 = 0 := by decide
lemma S4P213 : S4P 2 1 3 = F4.ew2 := by decide
lemma S4P220 : S4P 2 2 0 = 0 := by decide
lemma S4P221 : S4P 2 2 1 = 0 := by decide
lemma S4P222 : S4P 2 2 2 = 1 := by decide
lemma S4P223 : S4P 2 2 3 = F4.ew := by decide
lemma S4P230 : S4P 2 3 0 = 0 := by decide
lemma S4P231 : S4P 2 3 1 = 0 := by decide
lemma S4P232 : S4P 2 3 2 = 0 := by decide
lemma S4P233 : S4P 2 3 3 = 1 := by decide
lemma S4P300 : S4P 3 0 0 = 1 := by decide
lemma S4P301 : S4P 3 0 1 = F4.ew2 := by decide
lemma S4P302 : S4P 3 0 2 = F4.ew := by decide
lemma S4P303 : S4P 3 0 3 = 1 := by decide
lemma S4P310 : S4P 3 1 0 = 0 := by decide
lemma S4P311 : S4P 3 1 1 = 1 := by decide
lemma S4P312 : S4P 3 1 2 = 0 := by decide
lemma S4P313 : S4P 3 1 3 = F4.ew := by decide
lemma S4P320 : S4P 3 2 0 = 0 := by decide
lemma S4P321 : S4P 3 2 1 = 0 := by decide
lemma S4P322 : S4P 3 2 2 = 1 := by decide
lemma S4P323 : S4P 3 2 3 = F4.ew2 := by decide
lemma S4P330 : S4P 3 3 0 = 0 := by decide
lemma S4P331 : S4P 3 3 1 = 0 := by decide
lemma S4P332 : S4P 3 3 2 = 0 := by decide
lemma S4P333 : S4P 3 3 3 = 1 := by decide
lemma fxor00 : fxor 0 0 = 0 := by decide
lemma fxor01 : fxor 0 1 = 1 := by decide
lemma fxor02 : fxor 0 2 = 2 := by decide
lemma fxor03 : fxor 0 3 = 3 := by decide
lemma fxor10 : fxor 1 0 = 1 := by decide
lemma fxor11 : fxor 1 1 = 0 := by decide
lemma fxor12 : fxor 1 2 = 3 := by decide
lemma fxor13 : fxor 1 3 = 2 := by decide
lemma fxor20 : fxor 2 0 = 2 := by decide
lemma fxor21 : fxor 2 1 = 3 := by decide
lemma fxor22 : fxor 2 2 = 0 := by decide
lemma fxor23 : fxor 2 3 = 1 := by decide
lemma fxor30 : fxor 3 0 = 3 := by decide
lemma fxor31 : fxor 3 1 = 2 := by decide
lemma fxor32 : fxor 3 2 = 1 := by decide
lemma fxor33 : fxor 3 3 = 0 := by decide

lemma S4a0 : S4a 0 = 0 := rfl
lemma S4a1 : S4a 1 = 1 := rfl
lemma S4a2 : S4a 2 = F4.ew := rfl
lemma S4a3 : S4a 3 = F4.ew2 := rfl

lemma S4P_sq : ∀ h b' b'' : Fin 4, ∑ b, S4P h b' b * S4P h b b'' = if b' = b'' then 1 else 0 := by
  decide

lemma S4a_xor : ∀ c h : Fin 4, S4a (fxor c h) = S4a c + S4a h := by decide

lemma fxor_inj (h : Fin 4) : ∀ c c' : Fin 4, fxor c h = fxor c' h ↔ c = c' := by
  revert h; decide

lemma S4_frameM_shift (h c b : Fin 4) :
    frameM (fun _ => S4g) S4z (fxor c h) b = ∑ b', C (S4P h b' b) * frameM (fun _ => S4g) S4z c b' := by
  have h2 := ps4_two
  have hw := C_ew_sq
  simp only [frameM, S4z, S4a_xor, map_add, Fin.sum_univ_four]
  generalize C (S4a c) = A
  generalize S4g = g
  fin_cases h <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.val_zero, Fin.val_one,
      Fin.val_two, fin4_val3, S4P000, S4P001, S4P002, S4P003, S4P010, S4P011, S4P012, S4P013, S4P020, S4P021, S4P022, S4P023, S4P030, S4P031, S4P032, S4P033, S4P100, S4P101, S4P102, S4P103, S4P110, S4P111, S4P112, S4P113, S4P120, S4P121, S4P122, S4P123, S4P130, S4P131, S4P132, S4P133, S4P200, S4P201, S4P202, S4P203, S4P210, S4P211, S4P212, S4P213, S4P220, S4P221, S4P222, S4P223, S4P230, S4P231, S4P232, S4P233, S4P300, S4P301, S4P302, S4P303, S4P310, S4P311, S4P312, S4P313, S4P320, S4P321, S4P322, S4P323, S4P330, S4P331, S4P332, S4P333, S4a0, S4a1, S4a2, S4a3, F4.w, F4.w2, C_e0, C_e1, C_ew2,
      map_one, map_zero, pow_zero, pow_one, pow_two, pow_succ, mul_one, one_mul, zero_mul, mul_zero, add_zero,
      zero_add] <;>
    grind

lemma S4_G_shift (h b c' : Fin 4) :
    S4G b (fxor c' h) = ∑ b'', C (S4P h b b'') * S4G b'' c' := by
  have h2 := ps4_two
  have hw := C_ew_sq
  have e : ∀ b'' : Fin 4, C (S4P h b b'') * S4G b'' c' = (C (S4P h b b'') * tsemU (S4GpN b'' c')) * S4g⁻¹ := by
    intro b''; simp only [S4G]; ring
  simp only [e, ← Finset.sum_mul, S4G]
  congr 1
  rw [Fin.sum_univ_four]
  fin_cases h <;> fin_cases b <;> fin_cases c' <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, fxor00, fxor01, fxor02, fxor03, fxor10, fxor11, fxor12, fxor13, fxor20, fxor21, fxor22, fxor23, fxor30, fxor31, fxor32, fxor33, S4P000, S4P001, S4P002, S4P003, S4P010, S4P011, S4P012, S4P013, S4P020, S4P021, S4P022, S4P023, S4P030, S4P031, S4P032, S4P033, S4P100, S4P101, S4P102, S4P103, S4P110, S4P111, S4P112, S4P113, S4P120, S4P121, S4P122, S4P123, S4P130, S4P131, S4P132, S4P133, S4P200, S4P201, S4P202, S4P203, S4P210, S4P211, S4P212, S4P213, S4P220, S4P221, S4P222, S4P223, S4P230, S4P231, S4P232, S4P233, S4P300, S4P301, S4P302, S4P303, S4P310, S4P311, S4P312, S4P313, S4P320, S4P321, S4P322, S4P323, S4P330, S4P331, S4P332, S4P333,
      S4GpN00, S4GpN01, S4GpN02, S4GpN03, S4GpN10, S4GpN11, S4GpN12, S4GpN13, S4GpN20, S4GpN21, S4GpN22,
      S4GpN23, S4GpN30, S4GpN31, S4GpN32, S4GpN33, tsemU, lps_cons, lps_nil, F4.w, F4.w2, C_e0, C_e1,
      C_ew2, map_one, map_zero, pow_zero, pow_one, pow_two, pow_succ, mul_one, one_mul, zero_mul, mul_zero,
      add_zero, zero_add] <;>
    grind

lemma fxor_cancel : ∀ c c' : Fin 4, fxor (fxor c c') c' = c := by decide
lemma fxor_zero_left : ∀ c' : Fin 4, fxor 0 c' = c' := by decide

/-- **`thm:S4`, translation symmetry**: `D_i(l)[c][c'] = D_i(l)[c ⊕ c'][0]` (the member is symmetric under
the translations `z ↦ z + h`, `h ∈ 𝔽_4`; `⊕` = XOR of the codes). -/
theorem S4_rot (i l : ℕ) (c c' : Fin 4) :
    lawD (fun _ => S4g) S4z S4G i l c c' = lawD (fun _ => S4g) S4z S4G i l (fxor c c') 0 := by
  have h := lawD_conj (fun _ => S4g) S4z S4G (fun x => fxor x c') (S4P c')
    (fun c b => S4_frameM_shift c' c b) (fun b c'' => S4_G_shift c' b c'') (S4P_sq c')
    (fxor_inj c') i l (fxor c c') 0
  simp only [fxor_cancel, fxor_zero_left] at h
  exact h

end GeoSeq
