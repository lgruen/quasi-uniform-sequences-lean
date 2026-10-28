/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.LIconv
public import GeoSeq.T0
public import GeoSeq.Law

@[expose] public section

/-!
# GeoSeq stage S11: the characteristic-two counterexample (`rem:convchar2`), all levels

The instance `X = X' = 1`, `d_0 = 1`, `d_1 = ω` of the remark: `convL ω`, `L_c[n][i] =
d_{n+c} binom(2n+1-i, n-i)`. In characteristic two its rows are `η_{c,n} ≡ d_{n+c} e_{c,n}`
(`convL_scrDig`), so `B_c = diag(1/d_{i+c})`, and by `lem:ebasis` the carry responses are, at EVERY
level `K ≥ l ≥ 1`: own `D(l)[c][c] = -∑_{m=1}^{l} γ_m`, cross `D(l)[c][c'] = -1` (`γ` is even in
characteristic two, and `d` is 2-periodic). **`convchar2`**: the law is level-invariant, but the scramble is
self-similar for no scale `θ` (the diagonal `d_0, d_1, d_2 = 1, ω, 1` of `T_0` is not geometric when
`ω² ≠ 1`). This replaces the paper's computer check over `𝔽_4`, `K ≤ 6`, by a proof for all `K`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-- The diagonal `d_k` of the counterexample: `1` for even `k`, `ω` for odd `k`. -/
def convD (ω : F) (k : ℕ) : F := if k % 2 = 0 then 1 else ω

lemma convD_ne (ω : F) (hω : ω ≠ 0) (k : ℕ) : convD ω k ≠ 0 := by
  unfold convD; split_ifs <;> simp_all

lemma convD_add_two (ω : F) (k : ℕ) : convD ω (k + 2) = convD ω k := by
  simp [convD, Nat.add_mod_right]

lemma convD_parity (ω : F) (a b : ℕ) (h : a % 2 = b % 2) : convD ω a = convD ω b := by
  simp [convD, h]

lemma neg_one_eq_one_of_two (h2 : (2 : F) = 0) : (-1 : F) = 1 := by
  linear_combination -h2

/-- In characteristic two the rows of `convL ω` are `d_{n+c}` times the e-basis. -/
lemma convL_scrDig (h2 : (2 : F) = 0) (ω : F) (c : Fin 2) (n : ℕ) (V : F[X]) :
    scrDig (faurePl c) (convL ω c) n V = convD ω (n + c) * ebas c n V := by
  have hδ : faureDel c = (1 : F) := by
    fin_cases c
    · exact neg_one_eq_one_of_two h2
    · rfl
  rw [scrDig_tayl, ebas_tayl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := by simp at hi; omega
  rw [coeff_inv_pow _ (faureDel_sq c) _ _ (by omega), hδ, neg_one_eq_one_of_two h2, one_pow,
    one_pow, one_mul, one_mul, convL, convD,
    show n + 2 - 1 + (n - i) = 2 * n + 1 - i by omega, show n + 2 - 1 = n + 1 by omega,
    show (2 * n + 1 - i).choose (n + 1) = (2 * n + 1 - i).choose (n - i) by
      rw [Nat.choose_symm_of_eq_add]; omega]
  ring

/-- `B_c = diag(1/d_{i+c})` for the counterexample. -/
noncomputable def convB (ω : F) : Fin 2 → ℕ → ℕ → F :=
  fun c i j => if j = i then (convD ω (i + c))⁻¹ else 0

lemma convB_spec (h2 : (2 : F) = 0) (ω : F) (hω : ω ≠ 0) (c : Fin 2) (i : ℕ) (V : F[X]) :
    ebas c i V = ∑ j ∈ range (i + 1), convB ω c i j * scrDig (faurePl c) (convL ω c) j V := by
  rw [Finset.sum_eq_single i, convB, ite_eq_left rfl, convL_scrDig h2, ← mul_assoc,
    inv_mul_cancel₀ (convD_ne ω hω _), one_mul]
  · intro j _ hj; rw [convB, ite_eq_right hj, zero_mul]
  · intro h; simp at h

/-- The own coefficients of the counterexample: `-γ_{K-j}` at every level. -/
lemma convL_own (h2 : (2 : F) = 0) (ω : F) (hω : ω ≠ 0) (c : Fin 2) (K j : ℕ) (hj : j < K) :
    ownC (convB ω) c K j = -coeff (K - j) (gamF : PS) := by
  rw [ownC, Finset.sum_eq_single (K - j)]
  · rw [show K - (K - j) = j by omega, convB, ite_eq_left rfl, convB, ite_eq_left rfl]
    rcases Nat.even_or_odd (K - j) with ⟨r, hr⟩ | hodd
    · rw [convD_parity ω (j + c) (K + c) (by omega)]
      field_simp [convD_ne ω hω (K + c)]
    · rw [gamF_odd h2 _ (Nat.odd_iff.1 hodd)]; simp
  · intro n hn hnK
    simp only [mem_range] at hn
    rw [convB, ite_eq_right (by omega), mul_zero]
  · intro h; simp at h

/-- The cross coefficients of the counterexample: `-1` at depth `0`, else `0`, at every level. -/
lemma convL_cross (ω : F) (hω : ω ≠ 0) (c c' : Fin 2) (hcc : c' ≠ c) (K j : ℕ) (hK : 1 ≤ K) :
    crossC (convB ω) c c' K j = if j = K - 1 then -1 else 0 := by
  rw [crossC, convB, convB, ite_eq_left rfl]
  split_ifs with h
  · have hd : convD ω (K - 1 + c') = convD ω (K + c) := by
      fin_cases c <;> fin_cases c' <;> simp at hcc ⊢ <;>
        first | (congr 1; omega) | exact convD_parity ω _ _ (by omega)
    rw [hd]; field_simp [convD_ne ω hω (K + c)]
  · simp

/-- Partial sums from the coefficients by depth. -/
lemma partial_sum_eq (K : ℕ) (x y : ℕ → F) (hxy : ∀ n, n < K → x (K - 1 - n) = y n) :
    ∀ l, l ≤ K → ∑ j ∈ range K, (if K - l ≤ j then x j else 0) = ∑ n ∈ range l, y n := by
  intro l hl
  induction l with
  | zero => exact Finset.sum_eq_zero fun j hj => by simp at hj; rw [ite_eq_right (by omega)]
  | succ l ih =>
    have h := partial_diff K l (by omega) x
    rw [Finset.sum_range_succ, ← ih (by omega), ← hxy l (by omega)]
    linear_combination h

/-- **`rem:convchar2`** (characteristic two, every level): let `2 = 0` in the finite field `F` and
`ω ∉ {0, 1}` (such `ω` exists iff `q = 2^r ≥ 4`). The scramble `convL ω` of the Faure frame has nonzero
diagonal and a level-invariant law (`def:LI`; own responses `-∑_{m ≤ l} γ_m`, cross responses `-1` at
every level `K`), but it is self-similar for no scale `θ` and no multipliers. -/
theorem convchar2 [Fintype F] [DecidableEq F] (h2 : (2 : F) = 0) (ω : F) (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) :
    (∀ c n, convL ω c n n ≠ 0) ∧ LevelInv (scrGen faurePl (convL ω)) ∧
      ∀ θ : F, ∀ g : Fin 2 → PS, scrGen faurePl (convL ω) ≠ ssGen g (fun c => rescale θ (zF c)) := by
  have hdiag : ∀ c n, convL ω c n n ≠ 0 := by
    intro c n
    simp only [convL, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    split_ifs <;> simp [hω0]
  refine ⟨hdiag, ?_, ?_⟩
  · -- level invariance
    obtain ⟨D, -⟩ := exists_digitCode F
    have : NeZero (Fintype.card F) := ⟨Fintype.card_ne_zero⟩
    have hinj : Function.Injective (faurePl : Fin 2 → F) := by
      intro a b h; fin_cases a <;> fin_cases b <;> simp_all [faurePl]
    have hseq := t0 D faurePl hinj (convL ω) hdiag
    refine ⟨fun l c c' => if c' = c then -∑ m ∈ range l, coeff (m + 1) (gamF : PS) else -1,
      fun K l c c' hl hlK => ?_⟩
    have hK : 1 ≤ K := le_trans hl hlK
    obtain ⟨d, hd⟩ := carry_exists D _ K (hseq (2 * K) 0) 0 l c c'
    set c₁ : Fin 2 := if c = 0 then 1 else 0
    have hc₁ : c₁ ≠ c := by fin_cases c <;> simp [c₁]
    have hval := carry_val (convL ω) (convB ω) (convB_spec h2 ω hω0) K hK l c c₁ hc₁ c' d hd
    convert hd using 1
    rw [hval]
    split_ifs with hcc
    · subst hcc
      simp only [if_true]
      rw [partial_sum_eq K _ (fun n => -coeff (n + 1) (gamF : PS)) (fun n hn => by
        rw [convL_own h2 ω hω0 c' K _ (by omega), show K - (K - 1 - n) = n + 1 by omega]) l hlK,
        Finset.sum_neg_distrib]
    · have hc' : c' = c₁ := by fin_cases c <;> fin_cases c' <;> simp_all [c₁]
      simp only [hcc, if_false]
      rw [partial_sum_eq K _ (fun n => if n = 0 then -1 else 0) (fun n hn => by
        rw [convL_cross ω hω0 c c₁ hc₁ K _ hK]
        by_cases h0 : n = 0
        · simp [h0]
        · rw [ite_eq_right (by omega), ite_eq_right h0]) l hlK]
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun n _ => by simp)]
      simp
  · -- not self-similar
    intro θ g hss
    rw [scrGen_eq_ssGen_iff] at hss
    by_cases hθ : θ = 0
    · -- `θ = 0`: the digit `y_{0,1}(z) = ω` would vanish
      have h := hss 0 1 Polynomial.X
      have hz : rescale θ (zF 0 : PS) = 0 := by
        ext n; rw [coeff_rescale, hθ, map_zero]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [zF, constantCoeff_tRoot]
        · rw [zero_pow (by omega), zero_mul]
      rw [Polynomial.aeval_X, hz, mul_zero, map_zero, scrDig, Finset.sum_range_succ,
        Finset.sum_range_one] at h
      simp [convL, faurePl, convD, Polynomial.taylor_X] at h
      exact hω0 h
    · -- `θ ≠ 0`: `prop:LI`(a) forces a geometric diagonal of `T_0`
      have hT : ∀ c n V, scrDig (faurePl c) (convL ω c) n V = ∑ k ∈ range (n + 1),
          (if k = n then convD ω (n + c) else 0) * ebas c k V := by
        intro c n V
        rw [Finset.sum_eq_single n, ite_eq_left rfl, convL_scrDig h2]
        · intro k _ hk; rw [ite_eq_right hk, zero_mul]
        · intro h; simp at h
      have hg0 : constantCoeff (g 0) ≠ 0 := by
        intro h0
        have h := hss 0 0 1
        rw [map_one, mul_one, coeff_zero_eq_constantCoeff_apply, h0, scrDig,
          Finset.sum_range_one] at h
        simp [convL, convD] at h
      obtain ⟨lam, hlam, φ, hφ, hform⟩ := (LI_a (convL ω) _ hT θ hθ 0).1 ⟨g 0, hg0, hss 0⟩
      have e : ∀ n, convD ω n = lam * θ ^ n := by
        intro n
        have := hform n n le_rfl
        simp only [ite_eq_left, Fin.isValue, Fin.val_zero, add_zero, Nat.sub_self,
          coeff_zero_eq_constantCoeff_apply, hφ, mul_one] at this
        exact this
      have e0 := e 0; have e1 := e 1; have e2 := e 2
      simp [convD] at e0 e1 e2
      -- `lam = 1`, `θ = ω`, `θ² = 1`
      rw [← e0, one_mul] at e1 e2
      rw [← e1] at e2
      have : (ω - 1) ^ 2 = 0 := by linear_combination (-1 : F) * e2 + (1 - ω) * h2
      exact hω1 (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))

/-- **`rem:convchar2`, existence form**: in every finite field of characteristic two with `q ≥ 4`
elements there is a scramble of the Faure frame with a level-invariant law that is self-similar for no
scale. -/
theorem convchar2_exists [Fintype F] [DecidableEq F] (h2 : (2 : F) = 0) (hq : 4 ≤ Fintype.card F) :
    ∃ L : Fin 2 → ℕ → ℕ → F, (∀ c n, L c n n ≠ 0) ∧ LevelInv (scrGen faurePl L) ∧
      ∀ θ : F, ∀ g : Fin 2 → PS, scrGen faurePl L ≠ ssGen g (fun c => rescale θ (zF c)) := by
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ∉ ({0, 1} : Finset F) := by
    by_contra h
    push_neg at h
    have : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => h x
    have hc := Finset.card_le_card this
    rw [Finset.card_univ] at hc
    have := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨convL ω, convchar2 h2 ω hω.1 hω.2⟩

end GeoSeq
