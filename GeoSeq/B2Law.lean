/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Law

@[expose] public section

/-!
# GeoSeq stage S5: the law of the base-2 sequence (`thm:B2`, `eq:B2G`, `lem:octave`)

* `B2_root`: `u² + u = x` for `u = ∑_k x^{2^k}` over `𝔽_2` (Frobenius: `u² = u(x²)`, Mathlib
  `FiniteField.PowerSeries.expand_card`).
* `B2_frame_inv` (`eq:B2G`): `M G = G M = 1` for the frame matrix `M = frameM B2g B2z` and `G = B2G`.
* `B2_law`: `prop:law` applies (`w = z² + z`, `θ = 1`): the carry responses of `B2gen` are
  `lawD B2g B2z B2G i l` at every level.
* `B2_ghat`: the four coefficient formulas of `Ĝ = G/(1+x)` (`⌊log₂ n⌋ mod 2` patterns) of the proof
  of `lem:octave`.
* `B2_octave` (`lem:octave`, the type argument): for every `l ≥ 1` there is `1 ≤ l' ≤ 63` with the same
  `12`-digit responses `(D_i(l))_{i<12}`.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Powers of two and `u` -/

/-- `n` is a power of two. -/
def IsP2 (n : ℕ) : Prop := ∃ k, 2 ^ k = n

lemma u_of_isP2 {n : ℕ} (h : IsP2 n) : uB2coeff n = 1 := by
  obtain ⟨k, hk⟩ := h
  unfold uB2coeff
  rw [if_pos ⟨k, by rw [← hk]; exact Nat.lt_succ_of_lt Nat.lt_two_pow_self, hk⟩]

lemma u_of_not {n : ℕ} (h : ¬ IsP2 n) : uB2coeff n = 0 := by
  unfold uB2coeff
  rw [if_neg]
  rintro ⟨k, _, hk⟩; exact h ⟨k, hk⟩

lemma not_isP2_zero : ¬ IsP2 0 := by
  rintro ⟨k, hk⟩; exact absurd hk (by positivity)

lemma isP2_one : IsP2 1 := ⟨0, rfl⟩

lemma isP2_double (m : ℕ) (hm : 1 ≤ m) : IsP2 (2 * m) ↔ IsP2 m := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp at hk; omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ, hk]; ring⟩

lemma not_isP2_odd (n : ℕ) (hn : 3 ≤ n) (ho : n % 2 = 1) : ¬ IsP2 n := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · simp at hk; omega
  · rw [pow_succ] at hk; omega

lemma u_zero : uB2coeff 0 = 0 := u_of_not not_isP2_zero

lemma u_one : uB2coeff 1 = 1 := u_of_isP2 isP2_one

lemma u_double (m : ℕ) (hm : 1 ≤ m) : uB2coeff (2 * m) = uB2coeff m := by
  by_cases h : IsP2 m
  · rw [u_of_isP2 h, u_of_isP2 ((isP2_double m hm).mpr h)]
  · rw [u_of_not h, u_of_not (fun h' => h ((isP2_double m hm).mp h'))]

lemma u_odd (n : ℕ) (hn : 3 ≤ n) (ho : n % 2 = 1) : uB2coeff n = 0 :=
  u_of_not (not_isP2_odd n hn ho)

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

lemma ps2_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  rw [show (2 : PowerSeries (ZMod 2)) = C (2 : ZMod 2) from (map_ofNat C 2).symm]
  rw [show (2 : ZMod 2) = 0 from rfl, map_zero]

/-- Frobenius over `𝔽_2`: `[x^n] u² = [x^{n/2}] u` for even `n`, `0` for odd `n`. -/
lemma coeff_uB2_sq (n : ℕ) : coeff n (uB2 ^ 2) = if 2 ∣ n then uB2coeff (n / 2) else 0 := by
  have h : expand 2 two_ne_zero uB2 = uB2 ^ 2 := by
    convert FiniteField.PowerSeries.expand_card uB2 <;> exact (ZMod.card 2).symm
  rw [← h, coeff_expand]
  simp [uB2, coeff_mk]

/-- **`thm:B2`**: the lacunary series `u = ∑_k x^{2^k}` satisfies `u² + u = x` over `𝔽_2`. -/
theorem B2_root : uB2 ^ 2 + uB2 = X := by
  ext n
  rw [map_add, coeff_uB2_sq, coeff_X, uB2, coeff_mk]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos (by omega), show (m + m) / 2 = m by omega, if_neg (by omega)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [u_zero, add_zero]
    · rw [show m + m = 2 * m by ring, u_double m hm, zmod2_add_self]
  · rw [if_neg (by omega), zero_add]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [u_one]
    · rw [if_neg (by omega), u_odd _ (by omega) (by omega)]

/-! ## The frame matrix and its inverse (`eq:B2G`) -/

lemma X_mul_B2g1 : X * B2g 1 = uB2 := by
  ext n
  rcases n with _ | n
  · simp [B2g, uB2, coeff_mk, u_zero]
  · rw [coeff_succ_X_mul]; simp [B2g, uB2, coeff_mk]

lemma B2g1_mul : B2g 1 * (1 + uB2) = 1 := by
  have hX : (X : PowerSeries (ZMod 2)) ≠ 0 := X_ne_zero
  apply mul_left_cancel₀ hX
  rw [mul_one, ← mul_assoc, X_mul_B2g1]
  linear_combination B2_root

lemma one_add_X_inv : (1 + X : PowerSeries (ZMod 2))⁻¹ = PowerSeries.mk 1 := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  have h := mk_one_mul_one_sub_eq_one (S := ZMod 2)
  linear_combination h + (PowerSeries.mk 1 * X) * ps2_two

/-- **`eq:B2G`**: `M G = 1` and `G M = 1` for the frame matrix `M = ((g_0, g_0 u), (g_1, g_1(1+u)))`
of `thm:B2` and `G = B2G`. -/
theorem B2_frame_inv : frameM B2g B2z * B2G = 1 ∧ B2G * frameM B2g B2z = 1 := by
  have hMG : frameM B2g B2z * B2G = 1 := by
    have hv : (PowerSeries.mk fun n => uB2coeff (n + 1)) * (1 + uB2) = 1 := B2g1_mul
    have hXv : X * (PowerSeries.mk fun n => uB2coeff (n + 1)) = uB2 := X_mul_B2g1
    have hu := B2_root
    have hi : ((1 : PowerSeries (ZMod 2)) + X) * ((1 : PowerSeries (ZMod 2)) + X)⁻¹ = 1 := by
      rw [one_add_X_inv]
      have h := mk_one_mul_one_sub_eq_one (S := ZMod 2)
      linear_combination h + (PowerSeries.mk 1 * X) * ps2_two
    have h2 := ps2_two
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, frameM, B2g, B2z, B2G]
    · linear_combination (1 + X) * (1 + X)⁻¹ * uB2 * hv + (1 + 2 * uB2) * hi + uB2 * h2
    · linear_combination (1 + X) * (1 + uB2) * hu + (1 + X) * (1 + uB2) * X * h2
    · linear_combination (PowerSeries.mk fun n => uB2coeff (n + 1)) * (1 + X)⁻¹ * hv +
        (PowerSeries.mk fun n => uB2coeff (n + 1)) * (1 + X)⁻¹ * h2
    · linear_combination (1 + uB2) * hv + hXv + uB2 * h2
  exact ⟨hMG, mul_eq_one_comm.mp hMG⟩

/-! ## The law (`prop:law` with `w = z² + z`, `θ = 1`) -/

lemma B2_roots (c : Fin 2) :
    Polynomial.aeval (B2z c) (Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 2)) =
      PowerSeries.C (1 : ZMod 2) * X := by
  have hu := B2_root
  have h2 := ps2_two
  fin_cases c
  · simp [B2z, hu]
  · simp only [B2z, map_add, map_pow, Polynomial.aeval_X, map_one, one_mul]
    show (1 + uB2) ^ 2 + (1 + uB2) = X
    linear_combination hu + (1 + uB2) * h2

lemma B2_wdeg : (Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 2)).natDegree ≤ 2 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by rw [Polynomial.natDegree_X_pow]) (Polynomial.natDegree_X_le.trans (by norm_num)))

/-- **`thm:B2`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the base-2 sequence is `lawD B2g B2z B2G i l c c'` (independent of `K`). -/
theorem B2_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 2) :
    IsCarryEntry B2gen K i l c c' (lawD B2g B2z B2G i l c c') :=
  law B2g B2z _ B2_wdeg 1 1 (one_mul 1) B2_roots B2G B2_frame_inv.1 K i l hl hlK c c'

/-! ## The coefficients of `Ĝ = G/(1+x)` (proof of `lem:octave`) -/

lemma natCast_zmod2 (m : ℕ) : ((m : ℕ) : ZMod 2) = if m % 2 = 0 then 0 else 1 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> simp

lemma natCast_zmod2_congr {m m' : ℕ} (h : m % 2 = m' % 2) : ((m : ℕ) : ZMod 2) = (m' : ZMod 2) := by
  rw [natCast_zmod2, natCast_zmod2, h]

/-- `⌊log₂(n+1)⌋ = ⌊log₂ n⌋ + [n+1 is a power of two]` (`n ≥ 1`). -/
lemma log_succ_isP2 (n : ℕ) (hn : 1 ≤ n) (h : IsP2 (n + 1)) :
    Nat.log 2 (n + 1) = Nat.log 2 n + 1 := by
  obtain ⟨k, hk⟩ := h
  rcases k with _ | k
  · simp at hk; omega
  · rw [← hk, Nat.log_pow (by norm_num)]
    congr 1
    symm
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · rw [pow_succ] at hk; omega
    · omega

lemma log_succ_not (n : ℕ) (hn : 1 ≤ n) (h : ¬ IsP2 (n + 1)) :
    Nat.log 2 (n + 1) = Nat.log 2 n := by
  have h1 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) n
  apply Nat.log_eq_of_pow_le_of_lt_pow (by omega)
  rcases Nat.lt_or_ge (n + 1) (2 ^ (Nat.log 2 n + 1)) with h3 | h3
  · exact h3
  · exact absurd ⟨Nat.log 2 n + 1, by omega⟩ h

lemma log_succ_zmod (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.log 2 (n + 1) : ℕ) : ZMod 2) = (Nat.log 2 n : ZMod 2) + uB2coeff (n + 1) := by
  by_cases h : IsP2 (n + 1)
  · rw [log_succ_isP2 n hn h, u_of_isP2 h]; push_cast; rfl
  · rw [log_succ_not n hn h, u_of_not h, add_zero]

lemma coeff_mk_one_mul_mk_one (n : ℕ) :
    coeff n (PowerSeries.mk (1 : ℕ → ZMod 2) * PowerSeries.mk 1) = if n % 2 = 0 then 1 else 0 := by
  rw [coeff_mul_mk_one]
  simp only [coeff_mk, Pi.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [natCast_zmod2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]

/-- `∑_{t ≤ n} [x^t](1+u) = ⌊log₂ n⌋ mod 2` for `n ≥ 1`. -/
lemma sum_one_add_u (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ range (n + 1), coeff t (1 + uB2) = (Nat.log 2 n : ZMod 2) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [Finset.sum_range_succ, uB2, coeff_mk, u_zero, u_one]; decide
    · rw [Finset.sum_range_succ, ih hn', log_succ_zmod n hn']
      simp [uB2, coeff_mk]

/-- `[x^n] (u/x)/(1+x)²`: `1` for even `n`, `⌊log₂(n+1)⌋ mod 2` for odd `n`. -/
lemma coeff_v_mk_mk (n : ℕ) :
    coeff n (B2g 1 * PowerSeries.mk 1 * PowerSeries.mk 1) =
      if (n + 1) % 2 = 1 then 1 else ((Nat.log 2 (n + 1) : ℕ) : ZMod 2) := by
  -- partial sums
  set P : ℕ → ZMod 2 := fun t => coeff t (B2g 1 * PowerSeries.mk 1) with hP
  have hPs : ∀ t, P (t + 1) = P t + uB2coeff (t + 2) := fun t => by
    simp only [hP, coeff_mul_mk_one, Finset.sum_range_succ]
    simp [B2g, coeff_mk]
  have hF : ∀ n, coeff n (B2g 1 * PowerSeries.mk 1 * PowerSeries.mk 1) = ∑ t ∈ range (n + 1), P t :=
    fun n => coeff_mul_mk_one _ n
  have hP0 : P 0 = 1 := by simp [hP, coeff_mul_mk_one, B2g, coeff_mk, u_one]
  have hrec : ∀ n, coeff (n + 2) (B2g 1 * PowerSeries.mk 1 * PowerSeries.mk 1) =
      coeff n (B2g 1 * PowerSeries.mk 1 * PowerSeries.mk 1) + uB2coeff (n + 3) := fun n => by
    rw [hF, hF, Finset.sum_range_succ, Finset.sum_range_succ, hPs (n + 1)]
    have := zmod2_add_self (P (n + 1))
    linear_combination this
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [hF]; simp [hP0]
    · rw [hF]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [hPs 0, hP0, show uB2coeff (0 + 2) = 1 from u_of_isP2 ⟨1, rfl⟩]
      simp; decide
    · rw [hrec, ih n (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [if_pos (by omega), if_pos (by omega), u_odd _ (by omega) (by omega), add_zero]
      · rw [if_neg (by omega), if_neg (by omega)]
        rw [show n + 2 + 1 = (n + 2) + 1 by ring, log_succ_zmod (n + 2) (by omega),
          show n + 2 = (n + 1) + 1 by ring, log_succ_zmod (n + 1) (by omega),
          u_odd (n + 1 + 1) (by omega) (by omega), add_zero]

/-- **`lem:octave`, coefficient formulas** of `Ĝ = G/(1+x)` for `n ≥ 1`, read modulo `2`:
`[x^n] 1/(1+x²) = [n even]`, `[x^n] x/(1+x) = 1`, `[x^n](1+u)/(1+x) = ⌊log₂ n⌋`,
`[x^n] u/(x(1+x²)) = 1` for `n+1` odd and `⌊log₂(n+1)⌋` for `n+1` even. -/
theorem B2_ghat (n : ℕ) (hn : 1 ≤ n) :
    coeff n (B2G 0 0 * PowerSeries.mk 1) = (if n % 2 = 0 then 1 else 0) ∧
      coeff n (B2G 0 1 * PowerSeries.mk 1) = 1 ∧
      coeff n (B2G 1 1 * PowerSeries.mk 1) = ((Nat.log 2 n : ℕ) : ZMod 2) ∧
      coeff n (B2G 1 0 * PowerSeries.mk 1) =
        if (n + 1) % 2 = 1 then 1 else ((Nat.log 2 (n + 1) : ℕ) : ZMod 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show coeff n ((1 + X)⁻¹ * PowerSeries.mk 1) = _
    rw [one_add_X_inv, coeff_mk_one_mul_mk_one]
  · show coeff n (X * PowerSeries.mk 1) = _
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [coeff_succ_X_mul, coeff_mk, Pi.one_apply]
  · show coeff n ((1 + uB2) * PowerSeries.mk 1) = _
    rw [coeff_mul_mk_one, sum_one_add_u n hn]
  · show coeff n (B2g 1 * (1 + X)⁻¹ * PowerSeries.mk 1) = _
    rw [one_add_X_inv, coeff_v_mk_mk]

/-! ## The law in computable form -/

/-- Coefficients of the frame matrix `M = ((g_0, g_0 u), (g_1, g_1(1+u))) = (((1+x)(1+u), x + x²),
(u/x, 1))`. -/
def b2mco (c b : Fin 2) (a : ℕ) : ZMod 2 :=
  ![![if a = 0 then 1 else uB2coeff a + uB2coeff (a - 1) + (if a = 1 then 1 else 0),
      if a = 1 ∨ a = 2 then 1 else 0],
    ![uB2coeff (a + 1), if a = 0 then 1 else 0]] c b

/-- The coefficients of `Ĝ` (`B2_ghat`), valid for `n ≥ 1`. -/
def b2gh (b c' : Fin 2) (n : ℕ) : ZMod 2 :=
  ![![if n % 2 = 0 then 1 else 0, 1],
    ![if (n + 1) % 2 = 1 then 1 else ((Nat.log 2 (n + 1) : ℕ) : ZMod 2),
      ((Nat.log 2 n : ℕ) : ZMod 2)]] b c'

/-- The carry responses in computable form: `D_i(l) = I - ∑_{a ≤ i} M_a Ĝ_{l+i-a}`. -/
def b2lawC (i l : ℕ) (c c' : Fin 2) : ZMod 2 :=
  (if c = c' then 1 else 0) - ∑ a ∈ range (i + 1), ∑ b : Fin 2, b2mco c b a * b2gh b c' (l + i - a)

lemma coeff_frameM_B2 (c b : Fin 2) (a : ℕ) : coeff a (frameM B2g B2z c b) = b2mco c b a := by
  have hu := B2_root
  have h2 := ps2_two
  have e00 : frameM B2g B2z 0 0 = 1 * (1 + uB2) + X * (1 + uB2) := by
    simp only [frameM, B2g, Fin.isValue, Matrix.cons_val_zero, Fin.val_zero, pow_zero, mul_one]
    ring
  have e01 : frameM B2g B2z 0 1 = X + X ^ 2 := by
    simp only [frameM, B2g, B2z, Fin.isValue, Matrix.cons_val_zero, Fin.val_one, pow_one]
    linear_combination (1 + X) * hu
  have e10 : frameM B2g B2z 1 0 = B2g 1 := by simp [frameM]
  have e11 : frameM B2g B2z 1 1 = 1 := by
    simp only [frameM, B2z, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.val_one,
      pow_one]
    exact B2g1_mul
  fin_cases c <;> fin_cases b
  · simp only [Fin.zero_eta, Fin.isValue] at e00 ⊢
    rw [e00, map_add, one_mul]
    rcases a with _ | a
    · simp [b2mco, uB2, coeff_mk, u_zero]
    · rw [coeff_succ_X_mul]
      simp only [b2mco, uB2, map_add, coeff_one, coeff_mk]
      rcases a with _ | a
      · simp [u_zero]
      · simp
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e01 ⊢
    rw [e01, map_add, coeff_X, coeff_X_pow]
    simp only [b2mco]
    rcases a with _ | _ | _ | a <;> simp
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta] at e10 ⊢
    rw [e10]
    simp [B2g, b2mco, coeff_mk]
  · simp only [Fin.mk_one, Fin.isValue] at e11 ⊢
    rw [e11, coeff_one]
    simp [b2mco]

lemma coeff_ghat_B2 (b c' : Fin 2) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (B2G b c' * PowerSeries.mk 1) = b2gh b c' n := by
  obtain ⟨h00, h01, h11, h10⟩ := B2_ghat n hn
  fin_cases b <;> fin_cases c'
  · exact h00
  · exact h01
  · exact h10
  · exact h11

lemma lawD_B2 (i l : ℕ) (hl : 1 ≤ l) (c c' : Fin 2) :
    lawD B2g B2z B2G i l c c' = b2lawC i l c c' := by
  unfold lawD b2lawC
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b _ => ?_
  have : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [coeff_frameM_B2, coeff_ghat_B2 b c' _ (by omega)]

/-! ## The octave shift (`lem:octave`) -/

/-- The type of `l` for `j = 12`: the parity of `l` and the bits `⌊log₂ n⌋ mod 2`, `l ≤ n ≤ l + 12`. -/
def SameType (l l' : ℕ) : Prop :=
  l % 2 = l' % 2 ∧ ∀ t ≤ 12, Nat.log 2 (l + t) % 2 = Nat.log 2 (l' + t) % 2

lemma b2gh_congr (b c' : Fin 2) {n n' : ℕ} (hp : n % 2 = n' % 2)
    (h0 : Nat.log 2 n % 2 = Nat.log 2 n' % 2) (h1 : Nat.log 2 (n + 1) % 2 = Nat.log 2 (n' + 1) % 2) :
    b2gh b c' n = b2gh b c' n' := by
  fin_cases b <;> fin_cases c' <;>
    simp [b2gh, hp, natCast_zmod2_congr h0, natCast_zmod2_congr h1,
      show (n + 1) % 2 = (n' + 1) % 2 by omega]

lemma lawC_type {l l' : ℕ} (h : SameType l l') (i : ℕ) (hi : i < 12) (c c' : Fin 2) :
    b2lawC i l c c' = b2lawC i l' c c' := by
  unfold b2lawC
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b _ => ?_
  have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  congr 1
  rw [show l + i - a = l + (i - a) by omega, show l' + i - a = l' + (i - a) by omega]
  apply b2gh_congr
  · have := h.1; omega
  · exact h.2 _ (by omega)
  · rw [add_assoc, add_assoc]; exact h.2 _ (by omega)

lemma log_of (j m : ℕ) (h1 : 2 ^ j ≤ m) (h2 : m < 2 ^ (j + 1)) : Nat.log 2 m = j :=
  Nat.log_eq_of_pow_le_of_lt_pow h1 h2

/-- Every `l ≥ 64` has a smaller `l' ≥ 1` of the same type (`l' = 2^{k-2} + (l mod 2)` if the window
`[l, l+12]` lies in one octave `[2^k, 2^{k+1})`, `l' = l - 3·2^{k-1}` if it crosses `2^{k+1}`). -/
lemma octave_step (l : ℕ) (hl : 64 ≤ l) : ∃ l', 1 ≤ l' ∧ l' < l ∧ SameType l l' := by
  set k := Nat.log 2 l with hk
  have hk1 : 2 ^ k ≤ l := Nat.pow_log_le_self 2 (by omega)
  have hk2 : l < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) l
  have hk6 : 6 ≤ k := by
    rw [hk]; exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  clear_value k
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ k by omega)
  set P := 2 ^ m with hPdef
  have hP16 : 16 ≤ P := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hPdef] using this
  have e1 : 2 ^ (m + 1) = 2 * P := by rw [pow_succ]; ring
  have e2 : 2 ^ (m + 2) = 4 * P := by rw [pow_succ, pow_succ]; ring
  have e3 : 2 ^ (m + 2 + 1) = 8 * P := by rw [pow_succ, pow_succ, pow_succ]; ring
  have e4 : 2 ^ (m + 2 + 1 + 1) = 16 * P := by rw [pow_succ, pow_succ, pow_succ, pow_succ]; ring
  have hPe : P % 2 = 0 := by
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ m by omega)
    rw [hPdef, pow_succ]; omega
  rw [e2] at hk1; rw [e3] at hk2
  by_cases hw : l + 12 < 8 * P
  · refine ⟨P + l % 2, by omega, by omega, by omega, fun t ht => ?_⟩
    rw [log_of (m + 2) (l + t) (by omega) (by omega),
      log_of m (P + l % 2 + t) (by omega) (by omega)]
    omega
  · refine ⟨l - 6 * P, by omega, by omega, by omega, fun t ht => ?_⟩
    by_cases hlt : l + t < 8 * P
    · rw [log_of (m + 2) (l + t) (by omega) (by omega),
        log_of m (l - 6 * P + t) (by omega) (by omega)]
      omega
    · rw [log_of (m + 2 + 1) (l + t) (by omega) (by omega),
        log_of (m + 1) (l - 6 * P + t) (by omega) (by omega)]
      omega

/-- **`lem:octave`**: for every carry length `l ≥ 1` there is `1 ≤ l' ≤ 63` with the same `12`-digit
responses: `D_i(l) = D_i(l')` for all `i < 12` (hence for every `j ≤ 12`). -/
theorem B2_octave (l : ℕ) (hl : 1 ≤ l) :
    ∃ l', 1 ≤ l' ∧ l' ≤ 63 ∧ ∀ i < 12, ∀ c c' : Fin 2,
      lawD B2g B2z B2G i l c c' = lawD B2g B2z B2G i l' c c' := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    by_cases h63 : l ≤ 63
    · exact ⟨l, hl, h63, fun _ _ _ _ => rfl⟩
    · obtain ⟨l'', h1, h2, ht⟩ := octave_step l (by omega)
      obtain ⟨l', h1', h2', heq⟩ := ih l'' h2 h1
      refine ⟨l', h1', h2', fun i hi c c' => ?_⟩
      rw [lawD_B2 i l hl, lawC_type ht i hi, ← lawD_B2 i l'' h1, heq i hi c c']

end GeoSeq
