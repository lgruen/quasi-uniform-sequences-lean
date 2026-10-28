/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.DualThm

@[expose] public section

/-!
# GeoSeq stage S10: `thm:dual` (b), (c)

* `dual_p3` (kernel `decide`): over `𝔽_3`, distinct places and distinct parameters force collinear points
  (the paper: all six bijections of `𝔽_3` are affine).
* **`dual_b_example`**, **`dual_b`** (`thm:dual`(b)): for an odd prime `p`, admissible parameters exist iff
  `p ≥ 5`; example `a = (0, 1, a_2)`, `a_2 ∉ {0,1,2}`, `ξ = (0,1,2)`.
* **`dual_c`** (`thm:dual`(c)): if `a_0 ≠ a_1` (characteristic `≠ 2`), the projection `(C_0, C_1)` of `eq:dual`
  is not of the form `(L_0 P_{b_0} G, L_1 P_{b_1} G)` with `L_c` lower triangular and `G` upper triangular
  with nonzero diagonal (the products are finite sums by triangularity). The formal proof reads off the
  leading `3 × 3` blocks: rows 1 force `G[1][2] = -2b_c G[2][2]`, hence `b_0 = b_1`, and then row 0 forces
  `a_0 = a_1` (in fact also `ξ_0 = ξ_1`) — a slightly shorter route than the paper's normalisation.
-/

namespace GeoSeq

open Finset

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Over `𝔽_3`, distinct places and parameters force `det(1, a_c, ξ_c) = 0` (kernel `decide`). -/
theorem dual_p3 : ∀ a0 a1 a2 x0 x1 x2 : ZMod 3, a0 ≠ a1 → a0 ≠ a2 → a1 ≠ a2 →
    x0 ≠ x1 → x0 ≠ x2 → x1 ≠ x2 → (a1 - a0) * (x2 - x0) - (a2 - a0) * (x1 - x0) = 0 := by
  decide

lemma inj_fin3 {α : Type*} (f : Fin 3 → α) : Function.Injective f ↔
    f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
  constructor
  · intro h
    exact ⟨fun e => absurd (h e) (by decide), fun e => absurd (h e) (by decide),
      fun e => absurd (h e) (by decide)⟩
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

lemma zmod_cast_ne (p : ℕ) {n k : ℕ} (hn : n < p) (hk : k < p) (h : n ≠ k) :
    (n : ZMod p) ≠ (k : ZMod p) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk]; exact h

/-- **`thm:dual`(b), example**: for a prime `p ≥ 5` and `a_2 ∉ {0, 1, 2}`, the parameters `a = (0, 1, a_2)`,
`ξ = (0, 1, 2)` are admissible (`det = 2 - a_2`). -/
theorem dual_b_example (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a2 : ZMod p) (h0 : a2 ≠ 0) (h1 : a2 ≠ 1)
    (h2 : a2 ≠ 2) :
    Function.Injective (![0, 1, a2] : Fin 3 → ZMod p) ∧
      Function.Injective (![0, 1, 2] : Fin 3 → ZMod p) ∧
      Matrix.det !![1, (![0, 1, a2] : Fin 3 → ZMod p) 0, (![0, 1, 2] : Fin 3 → ZMod p) 0;
        1, (![0, 1, a2] : Fin 3 → ZMod p) 1, (![0, 1, 2] : Fin 3 → ZMod p) 1;
        1, (![0, 1, a2] : Fin 3 → ZMod p) 2, (![0, 1, 2] : Fin 3 → ZMod p) 2] ≠ 0 := by
  have c01 : (0 : ZMod p) ≠ 1 := by
    exact_mod_cast zmod_cast_ne p (n := 0) (k := 1) (by omega) (by omega) (by decide)
  have c02 : (0 : ZMod p) ≠ 2 := by
    exact_mod_cast zmod_cast_ne p (n := 0) (k := 2) (by omega) (by omega) (by decide)
  have c12 : (1 : ZMod p) ≠ 2 := by
    exact_mod_cast zmod_cast_ne p (n := 1) (k := 2) (by omega) (by omega) (by decide)
  refine ⟨(inj_fin3 _).2 ⟨by simpa using c01, by simpa using h0.symm, by simpa using h1.symm⟩,
    (inj_fin3 _).2 ⟨by simpa using c01, by simpa using c02, by simpa using c12⟩, ?_⟩
  rw [det_dual]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  intro h
  apply h2
  linear_combination -h

/-- **`thm:dual`(b)**: for an odd prime `p`, there are distinct places, distinct parameters and
non-collinear points `(a_c, ξ_c) ∈ 𝔽_p²` iff `p ≥ 5`. -/
theorem dual_b (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (∃ a ξ : Fin 3 → ZMod p, Function.Injective a ∧ Function.Injective ξ ∧
      Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] ≠ 0) ↔ 5 ≤ p := by
  constructor
  · rintro ⟨a, ξ, ha, hξ, hdet⟩
    by_contra h5
    have h2 := hp.out.two_le
    have hp3 : p = 3 := by
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp.out (by decide)
    subst hp3
    rw [inj_fin3] at ha hξ
    rw [det_dual] at hdet
    exact hdet (dual_p3 _ _ _ _ _ _ ha.1 ha.2.1 ha.2.2 hξ.1 hξ.2.1 hξ.2.2)
  · intro h5
    have h3 : (3 : ZMod p) ≠ 0 := by
      have := zmod_cast_ne p (n := 3) (k := 0) (by omega) (by omega) (by decide)
      exact_mod_cast this
    have h31 : (3 : ZMod p) ≠ 1 := by
      have := zmod_cast_ne p (n := 3) (k := 1) (by omega) (by omega) (by decide)
      exact_mod_cast this
    have h32 : (3 : ZMod p) ≠ 2 := by
      have := zmod_cast_ne p (n := 3) (k := 2) (by omega) (by omega) (by decide)
      exact_mod_cast this
    exact ⟨_, _, dual_b_example p h5 3 h3 h31 h32⟩

/-- **`thm:dual`(c)**: if `a_0 ≠ a_1` and `2 ≠ 0`, the projection `(C_0, C_1)` of `eq:dual` is not of the
form `(L_0 P_{b_0} G, L_1 P_{b_1} G)` with `L_c` lower triangular and `G` upper triangular with nonzero
diagonal: no sequence of `thm:dual` lies in the Faure orbit. -/
theorem dual_c {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a ξ : Fin 3 → F) (ha : a 0 ≠ a 1) :
    ¬ ∃ (L0 L1 G : ℕ → ℕ → F) (b0 b1 : F),
      (∀ n k, n < k → L0 n k = 0) ∧ (∀ n k, n < k → L1 n k = 0) ∧
      (∀ n k, k < n → G n k = 0) ∧ (∀ n, G n n ≠ 0) ∧
      (∀ n k, dualGen a ξ 0 n k =
        ∑ j ∈ range (n + 1), ∑ i ∈ range (k + 1), L0 n j * pas b0 j i * G i k) ∧
      (∀ n k, dualGen a ξ 1 n k =
        ∑ j ∈ range (n + 1), ∑ i ∈ range (k + 1), L1 n j * pas b1 j i * G i k) := by
  rintro ⟨L0, L1, G, b0, b1, hL0, hL1, hG, hGd, h0, h1⟩
  have g10 := hG 1 0 (by norm_num); have g20 := hG 2 0 (by norm_num); have g21 := hG 2 1 (by norm_num)
  have l01 := hL0 0 1 (by norm_num); have m01 := hL1 0 1 (by norm_num)
  -- the leading entries
  have e00 := h0 0 0; have e02 := h0 0 2; have e10 := h0 1 0; have e11 := h0 1 1; have e12 := h0 1 2
  have f00 := h1 0 0; have f02 := h1 0 2; have f10 := h1 1 0; have f11 := h1 1 1; have f12 := h1 1 2
  simp [dualGen, pas, Finset.sum_range_succ, g10, g20, g21] at e00 e02 e10 e11 e12 f00 f02 f10 f11 f12
  have hg0 := hGd 0; have hg1 := hGd 1; have hg2 := hGd 2
  -- row 1: `L[1][0] = 0`, `L[1][1] G[1][1] = 1`, `G[1][2] = -2 b G[2][2]`
  have l10 : L0 1 0 = 0 := by
    rcases e10 with h | h
    · exact h
    · exact absurd h hg0
  have m10 : L1 1 0 = 0 := by
    rcases f10 with h | h
    · exact h
    · exact absurd h hg0
  rw [l10] at e11 e12; rw [m10] at f11 f12
  simp only [zero_mul, zero_add] at e11 e12 f11 f12
  have l11 : L0 1 1 ≠ 0 := fun h => by rw [h, zero_mul] at e11; exact one_ne_zero e11
  have m11 : L1 1 1 ≠ 0 := fun h => by rw [h, zero_mul] at f11; exact one_ne_zero f11
  have q0 : G 1 2 + 2 * b0 * G 2 2 = 0 := by
    have : L0 1 1 * (G 1 2 + 2 * b0 * G 2 2) = 0 := by linear_combination -e12
    exact (mul_eq_zero.1 this).resolve_left l11
  have q1 : G 1 2 + 2 * b1 * G 2 2 = 0 := by
    have : L1 1 1 * (G 1 2 + 2 * b1 * G 2 2) = 0 := by linear_combination -f12
    exact (mul_eq_zero.1 this).resolve_left m11
  have hb : b0 = b1 := by
    have : (2 * G 2 2) * (b0 - b1) = 0 := by linear_combination q0 - q1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hg2))
  have hl : L0 0 0 = L1 0 0 := by
    have : (L0 0 0 - L1 0 0) * G 0 0 = 0 := by linear_combination f00 - e00
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hg0)
  apply ha
  rw [e02, f02, hb, hl]

end GeoSeq
