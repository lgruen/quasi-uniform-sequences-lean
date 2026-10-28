/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.K4Auto
public import GeoSeq.B3Law

@[expose] public section

/-!
# GeoSeq stage S8: the law of the Kummer sequence over `𝔽_4` (`thm:K4`)

* `K4_roots`, `K4_frame_inv`, `K4_law`: `prop:law` applies (`w = z³ - 1 = z³ + 1`, `θ = 1`;
  `G[b][c'] = ω^{-bc'} τ^{-b} g^{-1}`, the inverse of `M = diag(g) · (ω^{cb}) · diag(τ^b)`, since
  `∑_b ω^{b(c-c')} = 3 δ_{cc'} = δ_{cc'}` in characteristic two).
* `K4_net`: `t = 0` (`lem:t0` via `ss_t0`; places `1, ω, ω²`, `g(0) = 1`, `[x] z_c = ω^c`).
* `K4_rot`: the rotation symmetry `D_i(l)[c][c'] = D_i(l)[c - c'][0]` (indices mod `3`): the member
  is symmetric under `z ↦ ωz`, so one source coordinate suffices for the automaton.
* Closed forms in the basis `{1, τ^{-1}, τ^{-2}}` (`τ = (1+x)τ^{-2}`, `τ² = (1+x)τ^{-1}`,
  `τ³ = 1 + x`): `x g τ^b = K4Mn b` (`K4_M`), `x (1+x²) Ĝ[b][0] = K4An b` (`K4_ghat`).
* The initial states of `prop:automaton`: `esem4 (initS4 i c sh) = x^{8-i+sh} F_i[c][0]`, so the
  coefficient `l` of the state is `D_i(l)[c][0]` (`sh = 0`) resp. `D_i(l-1)[c][0]` (`sh = 1`)
  (`K4_init`, `K4_init1`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## `𝔽_4`-constants in power series -/

lemma C_e0 : (C F4.e0 : PowerSeries F4) = 0 := map_zero C
lemma C_e1 : (C F4.e1 : PowerSeries F4) = 1 := map_one C

/-- `ω² = ω + 1`. -/
lemma C_ew2 : (C F4.ew2 : PowerSeries F4) = C F4.ew + 1 := by
  rw [show F4.ew2 = F4.ew + 1 from rfl, map_add, map_one]

/-- `ω² + ω + 1 = 0`. -/
lemma C_ew_sq : (C F4.ew : PowerSeries F4) * C F4.ew = C F4.ew + 1 := by
  rw [← map_mul, show F4.ew * F4.ew = F4.ew + 1 from rfl, map_add, map_one]

lemma wpn_add (m n : ℕ) : wpn (m + n) = wpn m * wpn n := by
  unfold wpn
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> rcases hn with hn | hn | hn <;>
    simp [hm, hn, Nat.add_mod] <;> rfl

lemma wpn_pow (c b : ℕ) : wpn c ^ b = wpn (c * b) := by
  induction b with
  | zero => simp [wpn]
  | succ b ih => rw [pow_succ, ih, mul_add, mul_one, wpn_add]

lemma wpn_ne (n : ℕ) : wpn n ≠ 0 := by
  unfold wpn; split_ifs <;> decide

/-! ## The multiplier `g` -/

lemma tau4_add_ne (a : F4) (ha : a ≠ 1) : constantCoeff (tau4 + C a) ≠ 0 := by
  rw [map_add, tau4_const, constantCoeff_C]
  revert a; decide

lemma K4g_spec : K4g * (tau4 + C F4.w2) = C F4.w2 * (tau4 + C F4.w) := by
  have h := PowerSeries.inv_mul_cancel (tau4 + C F4.w2) (tau4_add_ne _ (by decide))
  unfold K4g
  linear_combination (C F4.w2 * (tau4 + C F4.w)) * h

lemma K4g_const : constantCoeff K4g = 1 := by
  unfold K4g
  rw [map_mul, map_mul, PowerSeries.constantCoeff_inv, map_add, map_add, tau4_const, constantCoeff_C,
    constantCoeff_C]
  rfl

lemma K4g_inv : K4g * K4g⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [K4g_const]; exact one_ne_zero)

/-! ## The law -/

lemma K4_roots (c : Fin 3) :
    Polynomial.aeval (K4z c) (Polynomial.X ^ 3 + 1 : Polynomial F4) = PowerSeries.C (1 : F4) * X := by
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one, one_mul, K4z]
  rw [mul_pow, ← map_pow, wpn_pow, tau4_cube]
  have h3 : wpn ((c : ℕ) * 3) = 1 := by unfold wpn; simp
  rw [h3, map_one, one_mul]
  linear_combination ps4_two

lemma K4_wdeg : (Polynomial.X ^ 3 + 1 : Polynomial F4).natDegree ≤ 3 := by
  rw [show (1 : Polynomial F4) = Polynomial.C 1 from rfl, Polynomial.natDegree_X_pow_add_C]

lemma frameM_K4 (c b : Fin 3) :
    frameM (fun _ => K4g) K4z c b = C (wpn ((c : ℕ) * b)) * (K4g * tau4 ^ (b : ℕ)) := by
  simp only [frameM, K4z]
  rw [mul_pow, ← map_pow, wpn_pow]; ring

lemma K4G_mk (b c' : Fin 3) :
    K4G b c' * PowerSeries.mk 1 = C (wpn (2 * b * c')) * (T4 ^ (b : ℕ) * K4g⁻¹ * PowerSeries.mk 1) := by
  simp only [K4G]; ring

lemma wpn_sum (c c' : Fin 3) :
    ∑ b : Fin 3, wpn ((c : ℕ) * b) * wpn (2 * b * c') = if c = c' then 1 else 0 := by
  fin_cases c <;> fin_cases c' <;> rfl

/-- **`thm:K4`**: `M G = 1` for the frame matrix `M[c][b] = g (ω^c τ)^b` and `G = K4G`. -/
theorem K4_frame_inv : frameM (fun _ => K4g) K4z * K4G = 1 := by
  ext1 c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ b : Fin 3, frameM (fun _ => K4g) K4z c b * K4G b c' =
      C (wpn ((c : ℕ) * b) * wpn (2 * b * c')) := by
    intro b
    rw [frameM_K4]
    have e : C (wpn ((c : ℕ) * b)) * (K4g * tau4 ^ (b : ℕ)) * K4G b c' =
        C (wpn ((c : ℕ) * b) * wpn (2 * b * c')) * (tau4 * T4) ^ (b : ℕ) * (K4g * K4g⁻¹) := by
      simp only [K4G]; rw [map_mul]; ring
    rw [e, tau4_T4, K4g_inv, one_pow, mul_one, mul_one]
  simp only [key, ← map_sum, wpn_sum]
  split_ifs <;> simp

/-- **`thm:K4`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the sequence is `lawD (fun _ => g) z G i l c c'` (independent of `K`). -/
theorem K4_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 3) :
    IsCarryEntry K4gen K i l c c' (lawD (fun _ => K4g) K4z K4G i l c c') :=
  law (fun _ => K4g) K4z _ K4_wdeg 1 1 (one_mul 1) K4_roots K4G K4_frame_inv K i l hl hlK c c'

/-! ## `t = 0` -/

/-- `τ = (1 + x) τ^{-2}`. -/
lemma tau4_eqT : tau4 = (1 + X) * T4 ^ 2 := by
  have h1 := tau4_T4
  have h2 := tau4_cube
  linear_combination (-(tau4 * (1 + tau4 * T4))) * h1 + T4 ^ 2 * h2

/-- The first `D` coefficients of `τ`. -/
def tau4L (D : ℕ) : List F4 := tmul D [1, 1] (tmul D (T4L D) (T4L D))

lemma tau4L_rep (D : ℕ) : TRep D (tau4L D) tau4 := by
  have h := tmul_rep (D := D) (a := [1, 1]) (φ := 1 + X) (fun n _ => by
    rcases n with _ | _ | n <;> simp [lget, coeff_X]) (tmul_rep (T4L_rep D) (T4L_rep D))
  intro n hn
  rw [tau4L, h n hn, tau4_eqT, pow_two]

lemma tau4_coeff1 : coeff 1 tau4 = 1 := by
  rw [← tau4L_rep 2 1 (by norm_num)]; decide

lemma K4_place : ssPlace K4z = fun c : Fin 3 => wpn (c : ℕ) := by
  funext c
  simp only [ssPlace, K4z, map_mul, constantCoeff_C, tau4_const, mul_one]

/-- **`thm:K4`** (`t = 0`): the sequence is a `(0,3)`-sequence in base `4`. -/
theorem K4_net : IsSeq0 f4code K4gen := by
  refine ss_t0 f4code (fun _ => K4g) K4z ?_ (fun c => by rw [K4g_const]; exact one_ne_zero) ?_
  · rw [K4_place]
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)
  · intro c
    simp only [K4z, coeff_C_mul, tau4_coeff1, mul_one]
    exact wpn_ne _

/-! ## Rotation symmetry -/

lemma wpn_rot : ∀ c c' b : Fin 3, wpn ((c : ℕ) * b) * wpn (2 * b * c') =
    wpn (((c - c' : Fin 3) : ℕ) * b) * wpn (2 * b * ((0 : Fin 3) : ℕ)) := by decide

/-- **`thm:K4`, rotation symmetry**: `D_i(l)[c][c'] = D_i(l)[c - c'][0]`. -/
theorem K4_rot (i l : ℕ) (c c' : Fin 3) :
    lawD (fun _ => K4g) K4z K4G i l c c' = lawD (fun _ => K4g) K4z K4G i l (c - c') 0 := by
  unfold lawD
  have hδ : (if c = c' then (1 : F4) else 0) = if c - c' = 0 then 1 else 0 := by
    revert c c'; decide
  rw [hδ]
  refine congrArg (fun t => (if c - c' = 0 then (1 : F4) else 0) - t) ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [frameM_K4, frameM_K4, K4G_mk, K4G_mk, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul]
  have hw := wpn_rot c c' b
  linear_combination (coeff a (K4g * tau4 ^ (b : ℕ)) *
    coeff (l + i - a) (T4 ^ (b : ℕ) * K4g⁻¹ * PowerSeries.mk 1)) * hw

/-! ## Closed forms in the basis `{1, τ^{-1}, τ^{-2}}` -/

lemma mk1_mul4 : (1 + X) * PowerSeries.mk (1 : ℕ → F4) = 1 := by
  have h := mk_one_mul_one_sub_eq_one (S := F4)
  rw [sub_eq_add_neg, neg4] at h
  rw [mul_comm]; exact h

lemma K4Mn0 : K4Mn 0 = ([.e1, .ew2], [.ew2, .ew2], [.ew, .ew]) := rfl
lemma K4Mn1 : K4Mn 1 = ([.ew2, .ew2], [.ew, .ew], [.e1, .ew, .ew2]) := rfl
lemma K4Mn2 : K4Mn 2 = ([.ew, .ew], [.e1, .ew, .ew2], [.ew2, .e0, .ew2]) := rfl
lemma K4An0 : K4An 0 = ([.e1, .ew2, .ew], [.ew, .e0, .ew], [.ew2, .e0, .ew2]) := rfl
lemma K4An1 : K4An 1 = ([.ew2, .ew2], [.e1, .ew2, .ew], [.ew, .e0, .ew]) := rfl
lemma K4An2 : K4An 2 = ([.ew, .ew], [.ew2, .ew2], [.e1, .ew2, .ew]) := rfl

/-- **`thm:K4`, the frame matrix in closed form**: `x g τ^b = P_0 + P_1 τ^{-1} + P_2 τ^{-2}` with the
numerators `K4Mn b`. -/
theorem K4_M (b : Fin 3) : X * (K4g * tau4 ^ (b : ℕ)) = tsem4 (K4Mn b) := by
  have hg := K4g_spec
  have h1 := tau4_T4
  have h3 := tau4_cube
  have h2 := ps4_two
  have hw := C_ew_sq
  simp only [F4.w, F4.w2, C_ew2] at hg
  fin_cases b <;>
    simp only [K4Mn0, K4Mn1, K4Mn2, tsem4, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail, lps_cons, lps_nil, F4.w, F4.w2,
      C_e0, C_e1, C_ew2, map_one, map_zero, mul_zero, add_zero, pow_zero, pow_one, mul_one] <;>
    grind

/-- **`thm:K4`, `Ĝ` in closed form**: `x (1 + x²) Ĝ[b][0] = P_0 + P_1 τ^{-1} + P_2 τ^{-2}` with the
numerators `K4An b`. -/
theorem K4_ghat (b : Fin 3) :
    X * lps Qp4 * (K4G b 0 * PowerSeries.mk 1) = tsem4 (K4An b) := by
  have hg := K4g_spec
  have hi := K4g_inv
  have h1 := tau4_T4
  have h3 := tau4_cube
  have h2 := ps4_two
  have hw := C_ew_sq
  have hm := mk1_mul4
  simp only [F4.w, F4.w2, C_ew2] at hg
  rw [K4G_mk, show 2 * ((b : Fin 3) : ℕ) * ((0 : Fin 3) : ℕ) = 0 by simp,
    show wpn 0 = 1 from rfl, map_one, one_mul]
  fin_cases b <;>
    simp only [K4An0, K4An1, K4An2, tsem4, Qp4, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail, lps_cons, lps_nil, F4.w, F4.w2,
      C_e0, C_e1, C_ew2, map_one, map_zero, mul_zero, add_zero, zero_add, pow_zero, pow_one, mul_one,
      one_mul] <;>
    grind

/-! ## The initial states -/

lemma K4mtab_eq (c b : Fin 3) (a : ℕ) (ha : a < 8) :
    coeff a (frameM (fun _ => K4g) K4z c b) = K4mtab c b a := by
  rw [frameM_K4, coeff_C_mul, K4mtab, ← coeff_succ_X_mul, K4_M, tsemL_rep 9 _ (a + 1) (by omega)]

lemma K4Mle_lps (i : ℕ) (hi : i < 8) (c b : Fin 3) :
    lps (K4Mle i c b) = ∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => K4g) K4z c b)) * X ^ a := by
  rw [K4Mle, lps_range_map]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [K4mtab_eq c b a (by have := Finset.mem_range.mp ha; omega)]

lemma K4_dQ : lps ([0, 1, 1] : List F4) = X * lps Qp4 * PowerSeries.mk 1 := by
  have hm := mk1_mul4
  rw [lps_Qp4]
  simp only [lps_cons, lps_nil, map_zero, map_one, mul_zero, add_zero, zero_add]
  linear_combination (-(X * (1 + X))) * hm

/-- **The initial states** (`prop:automaton`, proof): `esem4 (initS4 i c sh) = x^{8-i+sh} F_i[c][0]`. -/
theorem esem4_init (i : ℕ) (hi : i < 8) (c : Fin 3) (sh : ℕ) :
    esem4 (initS4 i c sh) = X ^ (8 - i + sh) * K4F i c 0 := by
  have g0 := K4_ghat 0
  have g1 := K4_ghat 1
  have g2 := K4_ghat 2
  have hQ := Qp4_unit
  have hdQ := K4_dQ
  have e8 : (X : PowerSeries F4) ^ (8 - i + sh) = X ^ (7 - i + sh) * X := by
    rw [← pow_succ]; congr 1; omega
  unfold esem4 initS4 K4F
  simp only [tsem4, initC, lps_trim, lps_pshift, lps_padd, lps_pmul, K4Mle_lps i hi, Fin.sum_univ_three,
    e8] at g0 g1 g2 ⊢
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => K4g) K4z c 0)) * X ^ a) = S0
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => K4g) K4z c 1)) * X ^ a) = S1
  generalize (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => K4g) K4z c 2)) * X ^ a) = S2
  generalize (X : PowerSeries F4) ^ (7 - i + sh) = k
  generalize (lps Qp4)⁻¹ = Qi at hQ ⊢
  by_cases hc : c = 0
  · simp only [hc, ite_true, lps_nil]
    linear_combination (k * Qi) * hdQ - (k * Qi * S0) * g0 - (k * Qi * S1) * g1 - (k * Qi * S2) * g2 +
      (k * X * (PowerSeries.mk 1 + (S0 * (K4G 0 0 * PowerSeries.mk 1) +
        S1 * (K4G 1 0 * PowerSeries.mk 1) + S2 * (K4G 2 0 * PowerSeries.mk 1)))) * hQ
  · simp only [hc, ite_false, lps_nil]
    linear_combination - (k * Qi * S0) * g0 - (k * Qi * S1) * g1 - (k * Qi * S2) * g2 +
      (k * X * ((S0 * (K4G 0 0 * PowerSeries.mk 1) +
        S1 * (K4G 1 0 * PowerSeries.mk 1) + S2 * (K4G 2 0 * PowerSeries.mk 1)))) * hQ

lemma f4_sub (x y : F4) : x - y = x + y := rfl

/-- Coefficient `n + i` of `F_i[c][c']` is the response `D_i(n)[c][c']` of `prop:law`. -/
theorem K4F_coeff (i : ℕ) (c c' : Fin 3) (n : ℕ) :
    coeff (n + i) (K4F i c c') = lawD (fun _ => K4g) K4z K4G i n c c' := by
  unfold K4F lawD
  rw [map_add, map_sum]
  have hsum : ∀ b : Fin 3, coeff (n + i)
      ((∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => K4g) K4z c b)) * X ^ a) *
        (K4G b c' * PowerSeries.mk 1)) =
      ∑ a ∈ range (i + 1), coeff a (frameM (fun _ => K4g) K4z c b) *
        coeff (n + i - a) (K4G b c' * PowerSeries.mk 1) := by
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

/-- **The initial states read the responses**: coefficient `l` of `initS4 i c 0` is `D_i(l)[c][0]`. -/
theorem K4_init (i : ℕ) (hi : i < 8) (c : Fin 3) (l : ℕ) :
    coeff (l + 8) (esem4 (initS4 i c 0)) = lawD (fun _ => K4g) K4z K4G i l c 0 := by
  rw [esem4_init i hi c 0, coeff_X_pow_mul', if_pos (by omega),
    show l + 8 - (8 - i + 0) = l + i by omega, K4F_coeff]

/-- Coefficient `l ≥ 1` of `initS4 i c 1` is `D_i(l-1)[c][0]`. -/
theorem K4_init1 (i : ℕ) (hi : i < 8) (c : Fin 3) (l : ℕ) (hl : 1 ≤ l) :
    coeff (l + 8) (esem4 (initS4 i c 1)) = lawD (fun _ => K4g) K4z K4G i (l - 1) c 0 := by
  rw [esem4_init i hi c 1, coeff_X_pow_mul', if_pos (by omega),
    show l + 8 - (8 - i + 1) = (l - 1) + i by omega, K4F_coeff]

end GeoSeq
