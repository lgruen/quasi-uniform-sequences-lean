/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Dual

@[expose] public section

/-!
# GeoSeq stage S10: `thm:dual`, part 2: the digits of `eq:dual` as Taylor coefficients

Group the index digits in pairs: `V_0(z) = ∑_k v_{2k} z^k`, `V_1(z) = ∑_k v_{2k+1} z^k` (`dualP0`,
`dualP1`). Then `y_{c,2k'} = [(z-a_c)^{k'}](V_0 + ξ_c V_1)` and `y_{c,2k'+1} = [(z-a_c)^{k'}] V_1`
(`dual_digit_even`, `dual_digit_odd`), Taylor coefficients being `Polynomial.taylor`.
Also `dvd_of_taylor` (`(X - a)^e ∣ f` from the vanishing of the first `e` Taylor coefficients) and
`taylor_coeff_split` (`[(z-a)^e] ((z-a)^e U H) = (U H)(a)`).
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F]

/-- `V_0(z) = ∑_k v_{2k} z^k`. -/
noncomputable def dualP0 {m : ℕ} (V : Fin m → F) : F[X] :=
  ∑ k : Fin m, if (k : ℕ) % 2 = 0 then monomial ((k : ℕ) / 2) (V k) else 0

/-- `V_1(z) = ∑_k v_{2k+1} z^k`. -/
noncomputable def dualP1 {m : ℕ} (V : Fin m → F) : F[X] :=
  ∑ k : Fin m, if (k : ℕ) % 2 = 1 then monomial ((k : ℕ) / 2) (V k) else 0

lemma taylor_monomial_coeff (r c : F) (j n : ℕ) :
    (taylor r (monomial j c)).coeff n = c * pas r n j := by
  rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow, pas]; ring

lemma taylor_dualP0_coeff {m : ℕ} (V : Fin m → F) (r : F) (n : ℕ) :
    (taylor r (dualP0 V)).coeff n =
      ∑ k : Fin m, if (k : ℕ) % 2 = 0 then V k * pas r n ((k : ℕ) / 2) else 0 := by
  rw [dualP0, map_sum, finset_sum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · exact taylor_monomial_coeff _ _ _ _
  · simp

lemma taylor_dualP1_coeff {m : ℕ} (V : Fin m → F) (r : F) (n : ℕ) :
    (taylor r (dualP1 V)).coeff n =
      ∑ k : Fin m, if (k : ℕ) % 2 = 1 then V k * pas r n ((k : ℕ) / 2) else 0 := by
  rw [dualP1, map_sum, finset_sum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · exact taylor_monomial_coeff _ _ _ _
  · simp

lemma dual_digit_even {s m : ℕ} (a ξ : Fin s → F) (V : Fin m → F) (c : Fin s) (k' : ℕ) :
    vecDigit (dualGen a ξ) V c (2 * k') =
      (taylor (a c) (dualP0 V + C (ξ c) * dualP1 V)).coeff k' := by
  rw [map_add, taylor_mul, taylor_C, coeff_add, coeff_C_mul, taylor_dualP0_coeff,
    taylor_dualP1_coeff, Finset.mul_sum, ← Finset.sum_add_distrib, vecDigit]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [dualGen, show 2 * k' / 2 = k' by omega, show 2 * k' % 2 = 0 by omega]
  rcases Nat.mod_two_eq_zero_or_one (k : ℕ) with h | h <;> simp [h] <;> ring

lemma dual_digit_odd {s m : ℕ} (a ξ : Fin s → F) (V : Fin m → F) (c : Fin s) (k' : ℕ) :
    vecDigit (dualGen a ξ) V c (2 * k' + 1) = (taylor (a c) (dualP1 V)).coeff k' := by
  rw [taylor_dualP1_coeff, vecDigit]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [dualGen, show (2 * k' + 1) / 2 = k' by omega, show (2 * k' + 1) % 2 = 1 by omega]
  rcases Nat.mod_two_eq_zero_or_one (k : ℕ) with h | h <;> simp [h] <;> ring

lemma dualP0_coeff {m : ℕ} (V : Fin m → F) (j : ℕ) :
    (dualP0 V).coeff j = if h : 2 * j < m then V ⟨2 * j, h⟩ else 0 := by
  rw [dualP0, finset_sum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨2 * j, h⟩]
    · simp
    · intro k _ hk
      split_ifs with h2
      · rw [coeff_monomial, if_neg]
        intro h3; apply hk; ext; simp only; omega
      · rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h2
    · rw [coeff_monomial, if_neg]; intro h3; have := k.isLt; omega
    · rfl

lemma dualP1_coeff {m : ℕ} (V : Fin m → F) (j : ℕ) :
    (dualP1 V).coeff j = if h : 2 * j + 1 < m then V ⟨2 * j + 1, h⟩ else 0 := by
  rw [dualP1, finset_sum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨2 * j + 1, h⟩]
    · simp [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
    · intro k _ hk
      split_ifs with h2
      · rw [coeff_monomial, if_neg]
        intro h3; apply hk; ext; simp only; omega
      · rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h2
    · rw [coeff_monomial, if_neg]; intro h3; have := k.isLt; omega
    · rfl

/-- `V = 0` iff `V_0 = V_1 = 0`. -/
lemma eq_zero_of_dualP {m : ℕ} (V : Fin m → F) (h0 : dualP0 V = 0) (h1 : dualP1 V = 0) : V = 0 := by
  funext k
  rcases Nat.mod_two_eq_zero_or_one (k : ℕ) with h | h
  · have := dualP0_coeff V ((k : ℕ) / 2)
    rw [h0, coeff_zero, dif_pos (by omega)] at this
    have e : (⟨2 * ((k : ℕ) / 2), by omega⟩ : Fin m) = k := by ext; simp only; omega
    rw [e] at this; exact this.symm
  · have := dualP1_coeff V ((k : ℕ) / 2)
    rw [h1, coeff_zero, dif_pos (by omega)] at this
    have e : (⟨2 * ((k : ℕ) / 2) + 1, by omega⟩ : Fin m) = k := by ext; simp only; omega
    rw [e] at this; exact this.symm

lemma taylor_X_sub_C_pow (a : F) (e : ℕ) : taylor a ((X - C a) ^ e) = X ^ e := by
  rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]

/-- The first `e` Taylor coefficients at `a` vanish ⟹ `(X - a)^e ∣ f`. -/
lemma dvd_of_taylor (a : F) (f : F[X]) (e : ℕ) (h : ∀ i < e, (taylor a f).coeff i = 0) :
    (X - C a) ^ e ∣ f := by
  obtain ⟨g, hg⟩ : X ^ e ∣ taylor a f := X_pow_dvd_iff.2 h
  refine ⟨taylor (-a) g, ?_⟩
  have h1 : f = taylor (-a) (taylor a f) := by rw [taylor_taylor, neg_add_cancel, taylor_zero]
  rw [h1, hg, taylor_mul, taylor_pow, taylor_X, map_neg, ← sub_eq_add_neg]

/-- `[(z-a)^e]((z-a)^e U H) = (U H)(a)`. -/
lemma taylor_coeff_split (a : F) (e : ℕ) (G : F[X]) :
    (taylor a ((X - C a) ^ e * G)).coeff e = G.eval a := by
  rw [taylor_mul, taylor_X_sub_C_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_eval_zero, taylor_eval, zero_add]

end GeoSeq
