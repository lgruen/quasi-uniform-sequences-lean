/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Two

@[expose] public section

/-!
# GeoSeq stage V9-6 (part 6): primes of the form `u² + 1` (`cor:gauss`)

`p = u² + 1` prime (`u ≥ 2`), `s = ℓ = 2`, places `(0, 1)`, `v = (-u, -1)`, `F_0 = ((-1, u), (-u, -1))`:
* `gauss_hNd`, `gauss_hrel`: the numerators `N_{0,1} = -1/u`, `N_{1,1} = 1/u²` solve (a);
* `gauss_design`: `sep(P_{4K}) ≥ √((u-2)² + (u²-u-1)²)/p` (the axis steps have a term `≥ (p-2)/p`, the diagonal steps
  the terms `(u-2)/p` and `(p-u-2)/p`);
* `gauss_lattice`: every nonzero `b ∈ Λ_{(u,-1)}` has `‖(|b| - 𝟏)_+‖_2 ≥ u - 1` (`Λ` is spanned by `(1,u)`, `(u,-1)`,
  `|b|² = (m² + n²) p`);
* **`gauss`** (`cor:gauss`): `(0,2)`; `sep(P_{4K}) ≥ √((u-2)² + (u²-u-1)²)/p ≥ 1 - (u+2)/p` (`u = √(p-1)`); the implied
  skeleton relation with `v̄ = (u, -1)` at every `P_{4K+1}` and `sep(P_{4K+1}) ≥ (u-1)/√p`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

lemma gauss_sq (u : ℕ) (hpu : p = u ^ 2 + 1) : (u : ZMod p) ^ 2 + 1 = 0 := by
  have h : ((u ^ 2 + 1 : ℕ) : ZMod p) = 0 := by rw [← hpu, ZMod.natCast_self]
  push_cast at h; exact h

lemma gauss_u_ne (u : ℕ) (hpu : p = u ^ 2 + 1) : (u : ZMod p) ≠ 0 := by
  intro h
  have := gauss_sq u hpu
  rw [h] at this
  simp at this

lemma gauss_hNd (u : ℕ) (hpu : p = u ^ 2 + 1) (c : Fin 2) (n : ℕ) (hn : n + 2 ≤ 2) :
    ∃ N', gaussN ((u : ℤ) : ZMod p) c (2 - 1 - n) = (X - C (faurePl c)) ^ n * N' ∧ N'.eval (faurePl c) ≠ 0 := by
  obtain rfl : n = 0 := by omega
  have hu := gauss_u_ne u hpu
  refine ⟨gaussN ((u : ℤ) : ZMod p) c 1, by simp, ?_⟩
  unfold gaussN
  split_ifs
  · simp only [eval_C, Int.cast_natCast]; exact neg_ne_zero.mpr (inv_ne_zero hu)
  · simp only [eval_C, Int.cast_natCast]; exact pow_ne_zero _ (inv_ne_zero hu)

/-- The multiplier identities (a) of `cor:gauss`, over any field with `u ≠ 0`, `u² + 1 = 0`. -/
lemma gauss_hrel_gen {F : Type*} [Field F] (u : ℤ) (hu : (u : F) ≠ 0) (hsq : (u : F) ^ 2 + 1 = 0)
    (c i : Fin 2) (h : i ≠ c) :
    wCoCo (faurePl : Fin 2 → F) c i = -C ((![-(u : F), -1] : Fin 2 → F) i) *
      ∑ n ∈ range (2 - 1), C (blockF (gaussF u) n i c) * gaussN (u : F) c (2 - 1 - n) := by
  have e01 : (univ.erase (0 : Fin 2)).erase 1 = ∅ := by decide
  have e10 : (univ.erase (1 : Fin 2)).erase 0 = ∅ := by decide
  fin_cases c <;> fin_cases i
  · exact absurd rfl h
  · show wCoCo faurePl 0 1 = _
    rw [wCoCo, e01, Finset.prod_empty]
    simp [blockF, gaussF, gaussN, ← map_neg, ← map_mul]
    rw [← map_one C]; congr 1; field_simp
  · show wCoCo faurePl 1 0 = _
    rw [wCoCo, e10, Finset.prod_empty]
    simp [blockF, gaussF, gaussN, ← map_neg, ← map_mul]
    rw [← map_one C, ← map_intCast (C : F →+* F[X]) u, ← map_mul, ← map_mul]; congr 1; field_simp
  · exact absurd rfl h

lemma gauss_hrel (u : ℕ) (hpu : p = u ^ 2 + 1) (c i : Fin 2) (h : i ≠ c) :
    wCoCo (faurePl : Fin 2 → ZMod p) c i = -C ((![-((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) i) *
      ∑ n ∈ range (2 - 1), C (blockF (gaussF u) n i c) * gaussN ((u : ℤ) : ZMod p) c (2 - 1 - n) :=
  gauss_hrel_gen (F := ZMod p) u (by simpa using gauss_u_ne u hpu) (by simpa using gauss_sq u hpu) c i h

lemma gapR_back (e t : ℤ) (he : e = 1 ∨ e = -1) (het : e * t ≤ 0) (ht : |t| < p) :
    ((gapNum1 p e (t : ZMod p) : ℕ) : ℝ) = p - |(t : ℝ)| - 1 := by
  have h := gap_back (p := p) e t he het ht
  have h2 : (((gapNum1 p e (t : ZMod p) : ℕ) : ℤ) : ℝ) = ((p - |t| - 1 : ℤ) : ℝ) := by rw [h]
  push_cast at h2; exact h2

lemma gapR_fwd (e t : ℤ) (he : e = 1 ∨ e = -1) (het : 0 < e * t) (ht : |t| < p) :
    ((gapNum1 p e (t : ZMod p) : ℕ) : ℝ) = |(t : ℝ)| - 1 := by
  have h := gap_fwd (p := p) e t he het ht
  have h2 : (((gapNum1 p e (t : ZMod p) : ℕ) : ℤ) : ℝ) = ((|t| - 1 : ℤ) : ℝ) := by rw [h]
  push_cast at h2; exact h2

/-- The target of `cor:gauss` at the design levels is at most `(p-2)/p`. -/
lemma gauss_target_le (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) :
    Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ≤ ((p : ℝ) - 2) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpR : (p : ℝ) = (u : ℝ) ^ 2 + 1 := by rw [hpu]; push_cast; ring
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu
  refine div_le_div_of_nonneg_right ?_ hp0.le
  rw [Real.sqrt_le_left (by rw [hpR]; nlinarith)]
  rw [hpR]; nlinarith

/-- The diagonal steps of `cor:gauss`: a forward coordinate with `|σ| = u - 1` and a backward one with `|σ| = u + 1`. -/
lemma gauss_diag (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (e σ : Fin 2 → ℤ) (i j : Fin 2) (hij : i ≠ j)
    (hei : e i = 1 ∨ e i = -1) (hej : e j = 1 ∨ e j = -1) (hfi : 0 < e i * σ i) (hσi : |σ i| = u - 1)
    (hbj : e j * σ j ≤ 0) (hσj : |σ j| = u + 1) :
    Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ≤
      Real.sqrt (∑ k, ((gapNum1 p (e k) (σ k : ZMod p) : ℝ) / p) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpR : (p : ℝ) = (u : ℝ) ^ 2 + 1 := by rw [hpu]; push_cast; ring
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hpZ : ((u : ℤ) + 1) < p := by rw [hpu]; push_cast; nlinarith
  have hgi := gapR_fwd (p := p) (e i) (σ i) hei hfi (by rw [hσi]; omega)
  have hgj := gapR_back (p := p) (e j) (σ j) hej hbj (by rw [hσj]; omega)
  have hai : |(σ i : ℝ)| = u - 1 := by
    rw [← Int.cast_abs, hσi]; push_cast; ring
  have haj : |(σ j : ℝ)| = u + 1 := by
    rw [← Int.cast_abs, hσj]; push_cast; ring
  have hsum : ∑ k, ((gapNum1 p (e k) (σ k : ZMod p) : ℝ) / p) ^ 2 =
      ((gapNum1 p (e i) (σ i : ZMod p) : ℝ) / p) ^ 2 + ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2 := by
    have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Fin.sum_univ_two]
    · rw [Fin.sum_univ_two, add_comm]
  rw [hsum, hgi, hgj, hai, haj, div_pow, div_pow, ← add_div, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hp0.le]
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (le_of_eq ?_)) hp0.le
  rw [hpR]; ring

lemma gsig0 (u : ℤ) (e : Fin 2 → ℤ) : gsig u e 0 = -e 0 + e 1 * u := by
  simp [gsig, gaussF, Fin.sum_univ_two]

lemma gsig1 (u : ℤ) (e : Fin 2 → ℤ) : gsig u e 1 = -(e 0 * u) - e 1 := by
  simp [gsig, gaussF, Fin.sum_univ_two]; ring

/-- **`cor:gauss`, the design levels** (one-digit relaxation): every step has a term
`≥ √((u-2)² + (u²-u-1)²)/p`. -/
theorem gauss_LB (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (K : ℕ) (e : Fin 2 → ℤ) (l : Fin 2 → ℕ)
    (hst : IsStep (2 * K) e l) :
    Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (2 - 1)), blockF (gaussF u) n i c') : ℝ) / p) ^ 2) := by
  obtain ⟨he, hne, hl⟩ := hst
  have hp3 : 3 ≤ p := by rw [hpu]; nlinarith
  have hσ : ∀ i, (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (2 - 1)), blockF (gaussF u) n i c') =
      ((gsig u e i : ℤ) : ZMod p) := by
    intro i
    unfold gsig
    push_cast
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [show min (l c') (2 - 1) = 1 by have := hl c'; omega, Finset.sum_range_one]
    rfl
  simp_rw [hσ]
  have hT := gauss_target_le (p := p) u hu hpu
  have h0 : e 0 = -1 ∨ e 0 = 0 ∨ e 0 = 1 := by have := he 0; omega
  have h1 : e 1 = -1 ∨ e 1 = 0 ∨ e 1 = 1 := by have := he 1; omega
  have hu' : (2 : ℤ) ≤ u := by exact_mod_cast hu
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1
  · -- (-1, -1)
    refine gauss_diag u hu hpu e (gsig u e) 0 1 (by decide) (Or.inr h0) (Or.inr h1) ?_ ?_ ?_ ?_
    · rw [gsig0, h0, h1]; nlinarith
    · rw [gsig0, h0, h1, abs_of_neg (by nlinarith)]; ring
    · rw [gsig1, h0, h1]; nlinarith
    · rw [gsig1, h0, h1, abs_of_pos (by nlinarith)]; ring
  · -- (-1, 0)
    exact hT.trans (cert_back1 hp3 e (gsig u e) 0 (Or.inr h0) (by rw [gsig0, h0, h1]; norm_num)
      (by rw [gsig0, h0, h1]; norm_num))
  · -- (-1, 1)
    refine gauss_diag u hu hpu e (gsig u e) 1 0 (by decide) (Or.inl h1) (Or.inr h0) ?_ ?_ ?_ ?_
    · rw [gsig1, h0, h1]; nlinarith
    · rw [gsig1, h0, h1, abs_of_pos (by nlinarith)]; ring
    · rw [gsig0, h0, h1]; nlinarith
    · rw [gsig0, h0, h1, abs_of_pos (by nlinarith)]; ring
  · -- (0, -1)
    exact hT.trans (cert_back1 hp3 e (gsig u e) 1 (Or.inr h1) (by rw [gsig1, h0, h1]; norm_num)
      (by rw [gsig1, h0, h1]; norm_num))
  · exfalso; obtain ⟨c, hc⟩ := hne; fin_cases c <;> simp_all
  · -- (0, 1)
    exact hT.trans (cert_back1 hp3 e (gsig u e) 1 (Or.inl h1) (by rw [gsig1, h0, h1]; norm_num)
      (by rw [gsig1, h0, h1]; norm_num))
  · -- (1, -1)
    refine gauss_diag u hu hpu e (gsig u e) 1 0 (by decide) (Or.inr h1) (Or.inl h0) ?_ ?_ ?_ ?_
    · rw [gsig1, h0, h1]; nlinarith
    · rw [gsig1, h0, h1, abs_of_neg (by nlinarith)]; ring
    · rw [gsig0, h0, h1]; nlinarith
    · rw [gsig0, h0, h1, abs_of_neg (by nlinarith)]; ring
  · -- (1, 0)
    exact hT.trans (cert_back1 hp3 e (gsig u e) 0 (Or.inl h0) (by rw [gsig0, h0, h1]; norm_num)
      (by rw [gsig0, h0, h1]; norm_num))
  · -- (1, 1)
    refine gauss_diag u hu hpu e (gsig u e) 0 1 (by decide) (Or.inl h0) (Or.inl h1) ?_ ?_ ?_ ?_
    · rw [gsig0, h0, h1]; nlinarith
    · rw [gsig0, h0, h1, abs_of_pos (by nlinarith)]; ring
    · rw [gsig1, h0, h1]; nlinarith
    · rw [gsig1, h0, h1, abs_of_neg (by nlinarith)]; ring

/-- The integer core of `gauss_lattice`: if `A² + B² ≥ 2(u² + 1)` then
`max(|A|-1,0)² + max(|B|-1,0)² ≥ (u-1)²`. -/
lemma jit_int (u A B : ℤ) (hu : 2 ≤ u) (h : 2 * (u ^ 2 + 1) ≤ A ^ 2 + B ^ 2) :
    (u - 1) ^ 2 ≤ (max (|A| - 1) 0) ^ 2 + (max (|B| - 1) 0) ^ 2 := by
  have hA2 : |A| ^ 2 = A ^ 2 := sq_abs A
  have hB2 : |B| ^ 2 = B ^ 2 := sq_abs B
  set a := |A| with ha
  set b := |B| with hb
  have ha0 : 0 ≤ a := abs_nonneg A
  have hb0 : 0 ≤ b := abs_nonneg B
  rw [← hA2, ← hB2] at h
  rcases Int.lt_or_le a 1 with ha1 | ha1
  · have hz : a = 0 := by omega
    rw [hz] at h ⊢
    have hbu : u + 1 ≤ b := by nlinarith
    rw [show max ((0 : ℤ) - 1) 0 = 0 by norm_num, max_eq_left (by omega)]
    nlinarith
  · rcases Int.lt_or_le b 1 with hb1 | hb1
    · have hz : b = 0 := by omega
      rw [hz] at h ⊢
      have hau : u + 1 ≤ a := by nlinarith
      rw [show max ((0 : ℤ) - 1) 0 = 0 by norm_num, max_eq_left (by omega)]
      nlinarith
    · rw [max_eq_left (by omega), max_eq_left (by omega)]
      rcases Int.lt_or_le (a + b) (2 * u + 2) with hT | hT
      · nlinarith
      · nlinarith [sq_nonneg (a - b)]

/-- **The lattice of `cor:gauss`**: for `p = u² + 1` every nonzero `b ∈ Λ_{(u,-1)} = {u b_0 ≡ b_1}` has
`‖(|b| - 𝟏)_+‖_2 ≥ u - 1` (`Λ = ℤ(1,u) + ℤ(u,-1)`, `|b|² = (m² + n²) p`). -/
theorem gauss_lattice (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (b : Fin 2 → ℤ) (hb : b ≠ 0)
    (hlat : InLat (![((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) b) : (u : ℝ) - 1 ≤ jitNorm b := by
  have hu' : (2 : ℤ) ≤ u := by exact_mod_cast hu
  -- `p ∣ u b_0 - b_1`
  have hdvd : (p : ℤ) ∣ (u : ℤ) * b 0 - b 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    unfold InLat at hlat
    rw [Fin.sum_univ_two] at hlat
    push_cast
    have e1 : (![((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) 0 = ((u : ℤ) : ZMod p) := rfl
    have e2 : (![((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) 1 = -1 := rfl
    rw [e1, e2] at hlat
    have hn1 : (-1 : ZMod p) * ((b 1 : ℤ) : ZMod p) = -((b 1 : ℤ) : ZMod p) := neg_one_mul _
    rw [hn1] at hlat
    rw [Int.cast_natCast] at hlat
    rw [sub_eq_add_neg]; push_cast; exact hlat
  obtain ⟨n, hn⟩ := hdvd
  set m := b 0 - (u : ℤ) * n with hm
  have hpZ : (p : ℤ) = (u : ℤ) ^ 2 + 1 := by rw [hpu]; push_cast; ring
  have hb0 : b 0 = m + u * n := by rw [hm]; ring
  have hb1 : b 1 = u * m - n := by rw [hm]; linear_combination -hn - n * hpZ
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hcon; push Not at hcon
    apply hb; funext c; fin_cases c
    · show b 0 = 0; rw [hb0, hcon.1, hcon.2]; ring
    · show b 1 = 0; rw [hb1, hcon.1, hcon.2]; ring
  -- the jitter norm as an integer expression
  have hjit : jitNorm b = Real.sqrt ((((max (|b 0| - 1) 0) ^ 2 + (max (|b 1| - 1) 0) ^ 2 : ℤ) : ℝ)) := by
    unfold jitNorm; rw [Fin.sum_univ_two]; push_cast; rfl
  rw [hjit]
  apply Real.le_sqrt_of_sq_le
  have key : (u - 1 : ℤ) ^ 2 ≤ (max (|b 0| - 1) 0) ^ 2 + (max (|b 1| - 1) 0) ^ 2 := by
    by_cases hsmall : (m = 1 ∨ m = -1) ∧ n = 0 ∨ m = 0 ∧ (n = 1 ∨ n = -1)
    · have hone : ∀ x y : ℤ, |x| = u → (u - 1 : ℤ) ^ 2 ≤ (max (|x| - 1) 0) ^ 2 + (max (|y| - 1) 0) ^ 2 := by
        intro x y hx
        rw [hx, max_eq_left (by omega)]
        nlinarith [sq_nonneg (max (|y| - 1) 0)]
      rcases hsmall with ⟨hm1 | hm1, hn0⟩ | ⟨hm0, hn1 | hn1⟩
      · rw [add_comm]; exact hone _ _ (by rw [hb1, hm1, hn0]; simp)
      · rw [add_comm]; exact hone _ _ (by rw [hb1, hm1, hn0]; simp)
      · exact hone _ _ (by rw [hb0, hm0, hn1]; simp)
      · exact hone _ _ (by rw [hb0, hm0, hn1]; simp)
    · have h2 : 2 ≤ m ^ 2 + n ^ 2 := by
        rcases hmn with hm0 | hn0
        · by_contra hlt; push Not at hlt
          have : m ^ 2 = 1 ∧ n = 0 := by
            have h1 : 1 ≤ m ^ 2 := by have : 0 < m ^ 2 := by positivity
                                      omega
            constructor <;> nlinarith [sq_nonneg n, sq_nonneg m]
          apply hsmall; left
          refine ⟨?_, this.2⟩
          have := this.1
          have : (m - 1) * (m + 1) = 0 := by ring_nf; linarith
          rcases mul_eq_zero.mp this with h | h
          · left; linarith
          · right; linarith
        · by_contra hlt; push Not at hlt
          have : n ^ 2 = 1 ∧ m = 0 := by
            have h1 : 1 ≤ n ^ 2 := by have : 0 < n ^ 2 := by positivity
                                      omega
            constructor <;> nlinarith [sq_nonneg n, sq_nonneg m]
          apply hsmall; right
          refine ⟨this.2, ?_⟩
          have := this.1
          have : (n - 1) * (n + 1) = 0 := by ring_nf; linarith
          rcases mul_eq_zero.mp this with h | h
          · left; linarith
          · right; linarith
      have hnorm : b 0 ^ 2 + b 1 ^ 2 = (m ^ 2 + n ^ 2) * ((u : ℤ) ^ 2 + 1) := by rw [hb0, hb1]; ring
      exact jit_int u (b 0) (b 1) hu' (by rw [hnorm]; nlinarith)
  have : ((u : ℝ) - 1) ^ 2 = (((u : ℤ) - 1) ^ 2 : ℤ) := by push_cast; ring
  rw [this]; exact_mod_cast key

/-- The implied-relation data of `cor:gauss` over any field: `v̄ = (u, -1)` satisfies `v̄_i = v_i / w'(a_i)` and
`v̄ᵀ F_0 = 0` (using `u² + 1 = 0`). -/
lemma gauss_implied_gen {F : Type*} [Field F] (u : ℤ) (hsq : (u : F) ^ 2 + 1 = 0) :
    (∀ i, (![(u : F), -1] : Fin 2 → F) i = 1 * (![-(u : F), -1] : Fin 2 → F) i /
      (wCo (faurePl : Fin 2 → F) i).eval (faurePl i)) ∧
    (∀ n c, n + 2 ≤ 2 → ∑ i, (![(u : F), -1] : Fin 2 → F) i * blockF (gaussF u) n i c = 0) := by
  refine ⟨fun i => ?_, fun n c hn => ?_⟩
  · fin_cases i
    · show (u : F) = 1 * -(u : F) / (wCo faurePl 0).eval (faurePl 0)
      rw [wCo_faurePl_zero]; simp [faurePl]
    · show (-1 : F) = 1 * -1 / (wCo faurePl 1).eval (faurePl 1)
      rw [wCo_faurePl_one]; simp [faurePl]
  · obtain rfl : n = 0 := by omega
    fin_cases c <;> simp [blockF, gaussF, Fin.sum_univ_two]
    linear_combination hsq

/-- **`cor:gauss`**: let `p = u² + 1` be prime (`u ≥ 2`), `θ ≠ 0`. The block-periodic residue sequence with
`s = ℓ = 2`, places `(0, 1)`, `v = (-u, -1)`, `F_0 = ((-1, u), (-u, -1))` is a digital `(0,2)`-sequence with
`sep(P_{4K}) ≥ √((u-2)² + (u²-u-1)²)/p ≥ 1 - (u+2)/p` for every `K ≥ 1` (`u = √(p-1)`), and at every level `4K + 1`
the skeleton relation with `v̄ = (u, -1)` holds and `sep(P_{4K+1}) ≥ (u-1)/√p`. -/
theorem gauss (u : ℕ) (hu : 2 ≤ u) (hpu : p = u ^ 2 + 1) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (gaussGen u θ) ∧
      (∀ K, 1 ≤ K → SepAtLevel p 2 (2 * K) (seqPoint (zcode p) (gaussGen u θ))
        (Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p)) ∧
      1 - ((u : ℝ) + 2) / p ≤ Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ∧
      ∀ K, (∀ x, x < p ^ (2 * (2 * K + 1) - 1) →
          ∑ i, (![((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) i *
            seqDigit (zcode p) (gaussGen u θ) x i (2 * K) = 0) ∧
        SepAtPrefix p 2 (2 * (2 * K + 1) - 1) (seqPoint (zcode p) (gaussGen u θ))
          ((p : ℝ) ^ (-(1 / ((2 : ℕ) : ℝ))) * ((u : ℝ) - 1)) := by
  have ha := faurePl_injective_two (p := p)
  have hu0 := gauss_u_ne u hpu
  have hv : ∀ c, (![-((u : ℤ) : ZMod p), -1] : Fin 2 → ZMod p) c ≠ 0 := by
    intro c; fin_cases c
    · exact neg_ne_zero.mpr (by rw [Int.cast_natCast]; exact hu0)
    · have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
      exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hv1 : ∀ c, (1 : Fin 2 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := gauss_hNd (p := p) u hpu
  have hrel := gauss_hrel (p := p) u hpu
  have hseq : IsSeq0 (zcode p) (gaussGen u θ) :=
    blockGen_t0 θ 2 _ (blockF (gaussF u)) _ 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv1 hNd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpR : (p : ℝ) = (u : ℝ) ^ 2 + 1 := by rw [hpu]; push_cast; ring
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu
  refine ⟨hseq, fun K hK => ?_, ?_, fun K => ?_⟩
  · have hT := gauss_target_le (p := p) u hu hpu
    have hLB1 : Real.sqrt (((u : ℝ) - 2) ^ 2 + ((u : ℝ) ^ 2 - u - 1) ^ 2) / p ≤ 1 :=
      hT.trans (by rw [div_le_one hp0]; linarith)
    have h := block_sep faurePl ha θ hθ 2 le_rfl le_rfl _ hv (blockF (gaussF u)) _ 1 hv1 hNd hrel K hK
      _ (fun e l hst => gauss_LB u hu hpu K e l hst)
    rwa [min_eq_right hLB1] at h
  · rw [show 1 - ((u : ℝ) + 2) / p = ((u : ℝ) ^ 2 - u - 1) / p by rw [hpR]; field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ hp0.le
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ((u : ℝ) - 2)])
  · obtain ⟨hvb, hF⟩ := gauss_implied_gen (F := ZMod p) u (by simpa using gauss_sq u hpu)
    have himp := implied_sep faurePl ha θ hθ 2 le_rfl le_rfl _ hv (blockF (gaussF u)) _ 1 hv1 hNd hrel
      (![((u : ℤ) : ZMod p), -1]) 1 hvb hF K
    refine ⟨himp.1, ?_⟩
    exact skel_sepAtPrefix le_rfl _ hseq _ ((u : ℝ) - 1)
      (fun b hb hlat => gauss_lattice u hu hpu b hb hlat) (2 * K + 1) (by omega)
      (fun x hx => by rw [show 2 * K + 1 - 1 = 2 * K by omega]; exact himp.1 x hx)

end GeoSeq
