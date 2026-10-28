/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V97Defs
public import GeoSeq.V96Gauss

@[expose] public section

/-!
# GeoSeq stage V9-7 (part 1): corrected skeleton relations (`lem:corrS`)

* `ssResGen_vecPoly`: the digits of `ssResGen` are residues of the index polynomial.
* `ssResGen_t0`: a self-similar scramble in residue form with `N_c(a_c) ≠ 0 ≠ U_c(a_c)` and `θ ≠ 0` is a digital
  `(0,s)`-sequence.
* **`ssRes_corr`**, `ssRes_corr_seq` (**`lem:corrS`**): with the correction coefficients (`CorrTrunc`, `χ_{c,0} = 1`),
  `∑_c v_c [y_{c,K-1}(V) + ∑_{d=1}^{K-1} χ_{c,d} y_{c,K-1-d}(V)] = 0` for `deg V ≤ sK - 2`.
* `ssRes_modify`: the elementary change of a local multiplier `φ_c ↦ φ_c(1 + ε w^j)` changes the digits by
  `y'_{c,n} = y_{c,n} + ε θ^j y_{c,n-j}` (`n ≥ j`) and leaves `y_{c,n}`, `n < j`, unchanged (`prop:joint`(ii)).
* `corrTrunc_modify`: and it changes the correction coefficient `χ_{c,j}` by `-ε θ^j`, the others below `j` unchanged.
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F] {s : ℕ}

lemma ssResGen_vecPoly (a : Fin s → F) (θ : F) (N U : Fin s → F[X]) (c : Fin s) (n : ℕ) (f : ℕ → F) (m : ℕ) :
    ∑ j ∈ range m, ssResGen a θ N U c n j * f j =
      θ ^ (n + 1) * locRes (a c) (n + 1) (vecPoly f m * N c) (U c * wCo a c ^ (n + 1)) := by
  induction m with
  | zero => simp [vecPoly, locRes_zero_num]
  | succ m ih =>
    have hv : vecPoly f (m + 1) = vecPoly f m + C (f m) * X ^ m := by simp [vecPoly, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih, hv, add_mul, locRes_add, mul_assoc (C (f m)), locRes_C_mul, ssResGen]
    ring

/-- A self-similar scramble in residue form (`N_c(a_c) ≠ 0`, `U_c(a_c) ≠ 0`, `θ ≠ 0`, distinct places) is a digital
`(0,s)`-sequence. -/
theorem ssResGen_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X]) (hN : ∀ c, (N c).eval (a c) ≠ 0)
    (hU : ∀ c, (U c).eval (a c) ≠ 0) : IsSeq0 D (ssResGen a θ N U) := by
  have hrow : ∀ c n, ∃ L : ℕ → F, (∀ k, ssResGen a θ N U c n k =
      ∑ t ∈ range (n + 1), L t * pas (a c) t k) ∧ L n ≠ 0 := by
    intro c n
    refine ⟨fun t => θ ^ (n + 1) * PowerSeries.coeff (n - t) ((taylor (a c) (N c) : PowerSeries F) *
      (taylor (a c) (U c * wCo a c ^ (n + 1)) : PowerSeries F)⁻¹), fun k => ?_, ?_⟩
    · simp only [ssResGen]
      rw [locRes, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, taylor_mul, Polynomial.coe_mul, mul_assoc,
        coeff_mul_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.coeff_coe, coeff_taylor_X_pow]; ring
    · simp only [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        PowerSeries.constantCoeff_inv, constantCoeff_taylor, eval_mul, eval_pow]
      exact mul_ne_zero (pow_ne_zero _ hθ) (mul_ne_zero (hN c) (inv_ne_zero (mul_ne_zero (hU c)
        (pow_ne_zero _ (wCo_eval_ne a ha c)))))
  choose L hL hLd using hrow
  have hgen : ssResGen a θ N U = scrGen a L := by funext c n k; rw [hL c n k, scrGen]
  rw [hgen]
  exact t0 D a ha L hLd

lemma locRes_neg (a : F) (k : ℕ) (W U : F[X]) : locRes a k (-W) U = -locRes a k W U := by
  have := locRes_C_mul a (-1) k W U
  rwa [map_neg, map_one, neg_one_mul, neg_one_mul] at this

/-- A zero of order `≥ k` of the numerator kills a pole of order `k`. -/
lemma locRes_high (a : F) (k j : ℕ) (W U : F[X]) (h : k ≤ j) : locRes a k (W * (X - C a) ^ j) U = 0 := by
  have t := locRes_cancel_pow a 0 k (W * (X - C a) ^ (j - k)) U
  rw [zero_add, locRes_zero_k, mul_assoc, ← pow_add, show j - k + k = j by omega] at t
  exact t

/-- One correction term as a residue: `χ y_{c,K-1-d}(V) = θ^K Res_{a_c}(V N_c χ (w/θ)^d / (U_c w^K) dz)` (`d < K`). -/
lemma corr_term (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (c : Fin s) (K d : ℕ) (hd : d < K) (χ : F) (W : F[X]) :
    χ * (θ ^ (K - 1 - d + 1) * locRes (a c) (K - 1 - d + 1) (W * N c) (U c * wCo a c ^ (K - 1 - d + 1))) =
      θ ^ K * locRes (a c) K (W * N c * (C χ * (C θ⁻¹ * wPoly a) ^ d)) (U c * wCo a c ^ K) := by
  have hk : K - 1 - d + 1 = K - d := by omega
  rw [hk]
  have hwc := wCo_eval_ne a ha c
  rw [wPoly_eq a c, show W * N c * (C χ * (C θ⁻¹ * ((X - C (a c)) * wCo a c)) ^ d) =
      C (χ * θ⁻¹ ^ d) * ((W * N c * wCo a c ^ d) * (X - C (a c)) ^ d) by
        rw [mul_pow, mul_pow, map_mul, map_pow]; ring,
    locRes_C_mul, show K = (K - d) + d by omega, locRes_cancel_pow,
    show U c * wCo a c ^ (K - d + d) = wCo a c ^ d * (U c * wCo a c ^ (K - d)) by rw [pow_add]; ring,
    show W * N c * wCo a c ^ d = (W * N c) * wCo a c ^ d from rfl,
    locRes_cancel_unit _ _ _ _ _ (by rw [eval_pow]; exact pow_ne_zero _ hwc), show K - d + d - d = K - d by omega]
  rw [show θ ^ (K - d + d) = θ ^ (K - d) * θ ^ d by rw [pow_add]]
  have : θ ^ d * θ⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hθ, one_pow]
  linear_combination (-(χ * θ ^ (K - d) * locRes (a c) (K - d) (W * N c) (U c * wCo a c ^ (K - d)))) * this

/-- **`lem:corrS`**: for a self-similar scramble in residue form with correction coefficients up to order `K`
(`CorrTrunc`, `χ_{c,0} = 1`, so `v_c = 1/φ_c(a_c)`), every `V` with `deg V < m`, `m + 1 ≤ sK`, satisfies
`∑_c v_c [y_{c,K-1}(V) + ∑_{d=1}^{K-1} χ_{c,d} y_{c,K-1-d}(V)] = 0`. -/
theorem ssRes_corr (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (hU : ∀ c, (U c).eval (a c) ≠ 0) (v : Fin s → F) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ)
    (hK : 1 ≤ K) (htr : CorrTrunc a θ N U v χ K) (f : ℕ → F) (m : ℕ) (hm : m + 1 ≤ s * K) :
    ∑ c, v c * (∑ j ∈ range m, ssResGen a θ N U c (K - 1) j * f j +
      ∑ d ∈ Finset.Ico 1 K, χ c d * ∑ j ∈ range m, ssResGen a θ N U c (K - 1 - d) j * f j) = 0 := by
  set V := vecPoly f m with hV
  have hterm : ∀ c, v c * (∑ j ∈ range m, ssResGen a θ N U c (K - 1) j * f j +
      ∑ d ∈ Finset.Ico 1 K, χ c d * ∑ j ∈ range m, ssResGen a θ N U c (K - 1 - d) j * f j) =
      θ ^ K * resAt a (fun _ => K) V c := by
    intro c
    -- all terms `d < K` as one residue
    have hsum : ∑ j ∈ range m, ssResGen a θ N U c (K - 1) j * f j +
        ∑ d ∈ Finset.Ico 1 K, χ c d * ∑ j ∈ range m, ssResGen a θ N U c (K - 1 - d) j * f j =
        θ ^ K * locRes (a c) K (V * N c * ∑ d ∈ range K, C (χ c d) * (C θ⁻¹ * wPoly a) ^ d)
          (U c * wCo a c ^ K) := by
      have hsplit : ∀ g : ℕ → F, ∑ i ∈ range K, g i = g 0 + ∑ i ∈ Finset.Ico 1 K, g i := fun g => by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K)]
      rw [Finset.mul_sum, locRes_sum, Finset.mul_sum, hsplit]
      congr 1
      · rw [ssResGen_vecPoly, ← hV, hχ0 c, ← corr_term a ha θ hθ N U c K 0 (by omega) 1 V, one_mul, Nat.sub_zero]
      · refine Finset.sum_congr rfl fun d hd => ?_
        have hd' := Finset.mem_Ico.mp hd
        rw [ssResGen_vecPoly, ← hV, corr_term a ha θ hθ N U c K d (by omega) (χ c d) V]
    rw [hsum]
    obtain ⟨R, hR⟩ := htr c
    have t0' := locRes_cancel_pow (a c) 0 K (V * R) (U c * wCo a c ^ K)
    rw [zero_add, locRes_zero_k] at t0'
    have hvN : C (v c) * (V * N c * ∑ d ∈ range K, C (χ c d) * (C θ⁻¹ * wPoly a) ^ d) =
        V * U c - (V * R) * (X - C (a c)) ^ K := by
      rw [show V * U c - (V * R) * (X - C (a c)) ^ K = V * (U c - (X - C (a c)) ^ K * R) by ring, ← hR]; ring
    rw [show v c * (θ ^ K * locRes (a c) K (V * N c * ∑ d ∈ range K, C (χ c d) * (C θ⁻¹ * wPoly a) ^ d)
      (U c * wCo a c ^ K)) = θ ^ K * locRes (a c) K (C (v c) * (V * N c * ∑ d ∈ range K, C (χ c d) *
        (C θ⁻¹ * wPoly a) ^ d)) (U c * wCo a c ^ K) by rw [locRes_C_mul]; ring, hvN, sub_eq_add_neg,
      locRes_add, locRes_neg, t0', neg_zero, add_zero, locRes_cancel_unit _ _ _ _ _ (hU c), resAt, placeCo_const]
  rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, res_thm_zero a ha _ _ (by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have : V.natDegree ≤ m - 1 := vecPoly_natDegree f m
    have : 2 ≤ s * K := le_trans hs (Nat.le_mul_of_pos_right _ (by omega))
    omega), mul_zero]

/-- **`lem:corrS`** for the points: the corrected skeleton relation holds on `P_{sK-1}`. -/
theorem ssRes_corr_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (hs : 2 ≤ s) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X]) (hU : ∀ c, (U c).eval (a c) ≠ 0)
    (v : Fin s → F) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTrunc a θ N U v χ K) : CorrRel D (ssResGen a θ N U) v χ K := by
  intro x hx
  have hdig : ∀ c n, seqDigit D (ssResGen a θ N U) x c n =
      ∑ j ∈ range (s * K - 1), ssResGen a θ N U c n j * idxDigit D x j := fun c n =>
    seqDigit_eq_range D _ x c _ _ fun j hj => idxDigit_eq_zero D x j
      (digit_high x j (lt_of_lt_of_le hx (Nat.pow_le_pow_right (NeZero.pos q) hj)))
  simp_rw [hdig]
  have hsK : 2 ≤ s * K := le_trans hs (Nat.le_mul_of_pos_right _ (by omega))
  exact ssRes_corr hs a ha θ hθ N U hU v χ hχ0 K hK htr _ _ (by omega)

/-- **The elementary change of a local multiplier** (`prop:joint`(ii)): replacing `φ_c` by `φ_c (1 + ε w^j)` changes
digit `n` of coordinate `c` by `ε θ^j y_{c,n-j}` for `n ≥ j` and not at all for `n < j`. -/
theorem ssRes_modify (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (c : Fin s) (ε : F) (j : ℕ) (f : ℕ → F) (m n : ℕ) :
    ∑ k ∈ range m, ssResGen a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U c n k * f k =
      ∑ k ∈ range m, ssResGen a θ N U c n k * f k +
        if j ≤ n then ε * θ ^ j * ∑ k ∈ range m, ssResGen a θ N U c (n - j) k * f k else 0 := by
  have hwc := wCo_eval_ne a ha c
  rw [ssResGen_vecPoly, ssResGen_vecPoly, Function.update_self,
    show vecPoly f m * (N c * (1 + C ε * wPoly a ^ j)) = vecPoly f m * N c +
      C ε * ((vecPoly f m * N c * wCo a c ^ j) * (X - C (a c)) ^ j) by rw [wPoly_eq a c, mul_pow]; ring,
    locRes_add, locRes_C_mul, mul_add]
  congr 1
  split_ifs with hjn
  · rw [ssResGen_vecPoly, show n + 1 = (n - j + 1) + j by omega, locRes_cancel_pow,
      show U c * wCo a c ^ (n - j + 1 + j) = wCo a c ^ j * (U c * wCo a c ^ (n - j + 1)) by rw [pow_add]; ring,
      locRes_cancel_unit _ _ _ _ _ (by rw [eval_pow]; exact pow_ne_zero _ hwc),
      show θ ^ (n - j + 1 + j) = θ ^ j * θ ^ (n - j + 1) by rw [← pow_add]; congr 1; omega]
    ring
  · rw [locRes_high _ _ _ _ _ (by omega), mul_zero, mul_zero]

/-- The other coordinates are unchanged by the change of `φ_c`. -/
lemma ssRes_modify_other (a : Fin s → F) (θ : F) (N U : Fin s → F[X]) (c c' : Fin s) (h : c' ≠ c) (ε : F)
    (j : ℕ) : ssResGen a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U c' =
      ssResGen a θ N U c' := by
  funext n k; simp only [ssResGen, Function.update_of_ne h]

/-- **The change of the correction coefficients** (`prop:joint`(ii)): if `χ` are the correction coefficients of
`(N, U)` up to order `j + 1` (`χ_{c,0} = 1`, `j ≥ 1`), then for `φ_c (1 + ε w^j)` the coefficients up to order `j + 1` are
those of `φ_c` with `χ_{c,j}` replaced by `χ_{c,j} - ε θ^j`. -/
theorem corrTrunc_modify (a : Fin s → F) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X]) (v : Fin s → F)
    (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (j : ℕ) (hj : 1 ≤ j) (htr : CorrTrunc a θ N U v χ (j + 1))
    (c : Fin s) (ε : F) :
    CorrTrunc a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U v
      (Function.update χ c (Function.update (χ c) j (χ c j - ε * θ ^ j))) (j + 1) := by
  intro c'
  by_cases hc : c' = c
  · subst hc
    simp only [Function.update_self]
    set T := ∑ d ∈ range (j + 1), C (χ c' d) * (C θ⁻¹ * wPoly a) ^ d with hT
    have hT' : ∑ d ∈ range (j + 1), C (Function.update (χ c') j (χ c' j - ε * θ ^ j) d) *
        (C θ⁻¹ * wPoly a) ^ d = T - C ε * wPoly a ^ j := by
      rw [hT, Finset.sum_range_succ, Finset.sum_range_succ, Function.update_self]
      rw [Finset.sum_congr rfl fun d hd => by
        rw [Function.update_of_ne (by have := Finset.mem_range.mp hd; omega)]]
      have : (C θ⁻¹ * wPoly a) ^ j * C (θ ^ j) = wPoly a ^ j := by
        rw [mul_pow, mul_comm, ← mul_assoc, ← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hθ, one_pow,
          map_one, one_mul]
      rw [map_sub, map_mul, sub_mul, ← this]; ring
    rw [hT']
    -- `T - 1` is divisible by `w`
    have hT1 : wPoly a ∣ T - 1 := by
      rw [hT, Finset.sum_range_succ', hχ0, pow_zero, mul_one, map_one, add_sub_cancel_right]
      exact Finset.dvd_sum fun d _ => by
        rw [pow_succ]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_mul_left _ _) _) _
    obtain ⟨R1, hR1⟩ := hT1
    obtain ⟨R0, hR0⟩ := htr c'
    have hw : (X - C (a c')) ∣ wPoly a := ⟨wCo a c', wPoly_eq a c'⟩
    obtain ⟨Q, hQ⟩ := hw
    refine ⟨R0 - C (v c') * C ε * N c' * Q ^ (j + 1) * R1 + C (v c') * C ε ^ 2 * N c' * Q ^ (2 * j) *
      (X - C (a c')) ^ (j - 1), ?_⟩
    have e1 : U c' - C (v c') * (N c' * (1 + C ε * wPoly a ^ j)) * (T - C ε * wPoly a ^ j) =
        (U c' - C (v c') * N c' * T) - C (v c') * C ε * N c' * wPoly a ^ j * (T - 1) +
          C (v c') * C ε ^ 2 * N c' * wPoly a ^ (2 * j) := by ring
    rw [e1, hR0, hR1, hQ, show 2 * j = (j + 1) + (j - 1) by omega]
    simp only [mul_pow, pow_add]
    ring
  · simp only [Function.update_of_ne hc]
    exact htr c'

end GeoSeq
