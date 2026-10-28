/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99Defs
public import GeoSeq.V96Inst
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# GeoSeq stage V9-9 (part 1): general tools for `thm:block`(c)

* `hrel_of_eval`: identity (a) of `def:block` for factored design numerators (`ndPoly`) follows from its values at the
  `s - 1` places `a_j`, `j ≠ c` (both sides have degree `≤ s - 2`); `hNd_of_ndPoly`: the vanishing orders.
* `caSig`, `sig_cast`: the changes `σ_i = ∑_c e_c M^{(min(l_c,s-1)-1)}[i][c]` (integers) of a step.
* `LB_of_sq`: the term of a step from an integer inequality `(p - A - 1)² ≤ ∑_i f_1(e_i, σ_i)² p²`.
* **`dom_LB`** (the written argument of `thm:block`(c), diagonal dominance): for `p ≥ 5A + 4` every step has a term
  `≥ 1 - (A+1)/p`.
* **`caCheck_sound`**: soundness of the computable checker `caCheck` (`allFold_sound`, `caLeafSum_decode`,
  `caGap_eq`).
-/

namespace GeoSeq

open Finset Polynomial

/-! ## Identity (a) by evaluation, and the vanishing orders -/

section Alg
variable {F : Type*} [Field F] {s : ℕ}

lemma prod_erase_erase_ite (c i : Fin s) (f : Fin s → F) :
    ∏ i' ∈ (univ.erase c).erase i, f i' = ∏ i', if i' = c ∨ i' = i then 1 else f i' := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  congr 1
  ext x; simp [and_comm, not_or]

lemma natDegree_ndSum (cf : Fin s → ℕ → ℕ → F) (c : Fin s) (n m : ℕ) :
    (∑ k ∈ range m, C (cf c n k) * X ^ k).natDegree ≤ m - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  rw [mem_range] at hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- **Identity (a) of `def:block` by evaluation**: for factored numerators `ndPoly a cf`, the polynomial identity
`w_{c,i} = -v_i ∑_n F_n[i][c] N_{c,s-1-n}` (`i ≠ c`) follows from its values at the places `a_j`, `j ≠ c`. -/
theorem hrel_of_eval (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (Fd : ℕ → Fin s → Fin s → F) (cf : Fin s → ℕ → ℕ → F)
    (hev : ∀ c i, i ≠ c → ∀ j, j ≠ c →
      (∏ i' : Fin s, if i' = c ∨ i' = i then 1 else (a j - a i')) =
        -(v i) * ∑ n ∈ range (s - 1), Fd n i c * ((a j - a c) ^ n *
          ∑ k ∈ range (s - 1 - n), cf c n k * a j ^ k)) :
    ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * ndPoly a cf c (s - 1 - n) := by
  classical
  intro c i hic
  have hnd : ∀ n ∈ range (s - 1), C (Fd n i c) * ndPoly a cf c (s - 1 - n) =
      C (Fd n i c) * ((X - C (a c)) ^ n * ∑ k ∈ range (s - 1 - n), C (cf c n k) * X ^ k) := by
    intro n hn
    rw [mem_range] at hn
    unfold ndPoly
    rw [show s - 1 - (s - 1 - n) = n by omega]
  rw [Finset.sum_congr rfl hnd]
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((univ.erase c).image a)
  · rw [card_image_of_injective _ ha, card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin]
    have h1 : (wCoCo a c i).natDegree ≤ s - 2 := by
      unfold wCoCo
      refine (natDegree_prod_le _ _).trans ?_
      have : ∀ i' ∈ (univ.erase c).erase i, (X - C (a i')).natDegree ≤ 1 := fun i' _ =>
        (natDegree_X_sub_C (a i')).le
      refine (sum_le_sum this).trans ?_
      rw [sum_const, smul_eq_mul, mul_one, card_erase_of_mem (by simp [hic]), card_erase_of_mem (mem_univ c),
        card_univ, Fintype.card_fin]
      omega
    have h2 : (-C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * ((X - C (a c)) ^ n *
        ∑ k ∈ range (s - 1 - n), C (cf c n k) * X ^ k)).natDegree ≤ s - 2 := by
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_neg, natDegree_C, zero_add]
      apply natDegree_sum_le_of_forall_le
      intro n hn
      rw [mem_range] at hn
      refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      have := natDegree_ndSum cf c n (s - 1 - n)
      omega
    have h3 := (natDegree_sub_le _ _).trans (max_le h1 h2)
    refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast (show _ < s - 1 by omega).trans_le' h3
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    have hjc : j ≠ c := ne_of_mem_erase hj
    have := hev c i hic j hjc
    rw [← prod_erase_erase_ite] at this
    simp only [wCoCo, eval_prod, eval_sub, eval_X, eval_C, eval_mul, eval_neg, eval_finsetSum, eval_pow]
    rw [this]

/-- The vanishing orders of `def:block`(a) for factored numerators: `N_{c,s-1-n} = (z - a_c)^n N'_{c,n}` with
`N'_{c,n}(a_c) ≠ 0`, given the values `∑_k cf c n k a_c^k ≠ 0`. -/
theorem hNd_of_ndPoly (a : Fin s → F) (cf : Fin s → ℕ → ℕ → F)
    (hne : ∀ c n, n + 2 ≤ s → ∑ k ∈ range (s - 1 - n), cf c n k * a c ^ k ≠ 0) :
    ∀ c n, n + 2 ≤ s → ∃ N', ndPoly a cf c (s - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0 := by
  intro c n hn
  refine ⟨∑ k ∈ range (s - 1 - n), C (cf c n k) * X ^ k, ?_, ?_⟩
  · unfold ndPoly
    rw [show s - 1 - (s - 1 - n) = n by omega]
  · simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact hne c n hn

end Alg

/-! ## Small numbers, the changes of a step, and the term of a step -/

section Step
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- A `{2,3}`-smooth number is a unit modulo every prime `p ≥ 5`. -/
lemma zmod_smooth_ne (hp : 5 ≤ p) (k : ℕ) (hk : k ∣ 6 ^ 20) : (k : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hpr := (Fact.out : p.Prime)
  have h6 : p ∣ 2 * 3 := hpr.dvd_of_dvd_pow (h.trans hk)
  rcases (Nat.Prime.dvd_mul hpr).mp h6 with h' | h' <;> have := Nat.le_of_dvd (by norm_num) h' <;> omega

lemma zmod_ofNat_ne (hp : 5 ≤ p) (k : ℕ) [k.AtLeastTwo] (hk : k ∣ 6 ^ 20) :
    (OfNat.ofNat k : ZMod p) ≠ 0 := by
  rw [← Nat.cast_ofNat]; exact zmod_smooth_ne hp k hk

/-- Closes goals `¬ (n : ZMod p) = 0` (and conjunctions of them, possibly negated) for `{2,3}`-smooth numerals `n`,
given `h : 5 ≤ p`. -/
macro "smooth_ne " h:term : tactic =>
  `(tactic| ((repeat' (first | apply And.intro | rw [neg_eq_zero])) <;>
    exact zmod_ofNat_ne $h _ (by norm_num)))

/-- The changes `σ_i = ∑_c e_c M^{(min(l_c, s-1) - 1)}[i][c]` (integers) of the step `(e, l)` (`thm:block`(iii)). -/
def caSig (Mz : ℕ → Fin s → Fin s → ℤ) (e : Fin s → ℤ) (l : Fin s → ℕ) (i : Fin s) : ℤ :=
  ∑ c, e c * Mz (min (l c) (s - 1) - 1) i c

/-- The change of the geometric digit in `block_sep` is the integer change `σ_i`, read modulo `p`. -/
lemma sig_cast (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (e : Fin s → ℤ) (l : Fin s → ℕ) (hl : ∀ c, 1 ≤ l c) (i : Fin s) :
    (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') =
      ((caSig Mz e l i : ℤ) : ZMod p) := by
  unfold caSig
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 := hl c
  rw [hM (min (l c) (s - 1) - 1) (by omega) i c, show min (l c) (s - 1) - 1 + 1 = min (l c) (s - 1) by omega]
  simp [blockF]

/-- The term of a step from an integer inequality: `(p - A - 1)² ≤ ∑_i g_i²` gives
`1 - (A+1)/p ≤ (∑_i (g_i/p)²)^{1/2}`. -/
lemma LB_of_sq (A : ℕ) (g : Fin s → ℕ) (h : ((p : ℤ) - A - 1) ^ 2 ≤ ∑ i, ((g i : ℕ) : ℤ) ^ 2) : ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((g i : ℝ) / p) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hR : ((p : ℝ) - A - 1) ^ 2 ≤ ∑ i, ((g i : ℝ)) ^ 2 := by exact_mod_cast h
  apply Real.le_sqrt_of_sq_le
  have hsum : ∑ i, ((g i : ℝ) / p) ^ 2 = (∑ i, (g i : ℝ) ^ 2) / (p : ℝ) ^ 2 := by
    rw [Finset.sum_div]; simp [div_pow]
  rw [hsum, div_pow]
  exact div_le_div_of_nonneg_right hR (by positivity)

end Step

/-! ## The written argument: diagonal dominance (`thm:block`(c), "The bound") -/

section Dom
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **The bound of `thm:block`(c) for `p ≥ 5A + 4`** (diagonal dominance, the argument of geo `prop:D` with a jitter of
one unit): if every partial sum `M^{(j)}` has the diagonal `-α_c` and off-diagonal entries `|M^{(j)}[i][c]| ≤ B_{ic}`
with `∑_{c ≠ i} B_{ic} ≤ α_i ≤ A`, then every step has a term `≥ 1 - (A+1)/p`: an axis step along `c` has the backward
coordinate `σ_c = -e_c α_c`, and a step with two moving axes has two backward coordinates with `|σ| ≤ 2A`, and
`2 (p - 2A - 1)² ≥ (p - A - 1)²` for `p ≥ 5A + 4`. -/
theorem dom_LB (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (α : Fin s → ℤ) (Bd : Fin s → Fin s → ℤ) (A : ℕ)
    (hdiag : ∀ j, j + 2 ≤ s → ∀ i, Mz j i i = -α i)
    (hB : ∀ j, j + 2 ≤ s → ∀ i c, i ≠ c → |Mz j i c| ≤ Bd i c)
    (hdom : ∀ i, ∑ c ∈ univ.erase i, Bd i c ≤ α i) (hαA : ∀ i, α i ≤ A) (hp : 5 * A + 4 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2) := by
  rintro e l ⟨he, hne, hl⟩
  simp_rw [sig_cast hs Fz Mz hM e l (fun c => (hl c).1)]
  apply LB_of_sq
  set R : Fin s → ℤ := fun i => ∑ c ∈ univ.erase i, e c * Mz (min (l c) (s - 1) - 1) i c with hRdef
  have hsplit : ∀ i, caSig Mz e l i = e i * (-α i) + R i := by
    intro i
    unfold caSig
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hdiag _ (by have := (hl i).1; omega)]
  have hR : ∀ i, |R i| ≤ α i := by
    intro i
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun c hc => ?_).trans (hdom i))
    have hci : i ≠ c := fun h => (ne_of_mem_erase hc) h.symm
    rw [abs_mul]
    have h1 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
    have h2 := hB (min (l c) (s - 1) - 1) (by have := (hl c).1; omega) i c hci
    nlinarith [abs_nonneg (e c), abs_nonneg (Mz (min (l c) (s - 1) - 1) i c)]
  have hpA : (5 * A + 4 : ℤ) ≤ p := by exact_mod_cast hp
  -- a moving coordinate is backward with `|σ| ≤ α_i + |R_i|`
  have hgap : ∀ i, e i ≠ 0 → ((gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) : ℕ) : ℤ) =
      p - |caSig Mz e l i| - 1 ∧ |caSig Mz e l i| ≤ α i + |R i| := by
    intro i hi
    have hei : e i = 1 ∨ e i = -1 := by have := he i; omega
    have hRi := hR i
    have hαi := hαA i
    have hα0 : 0 ≤ α i := (abs_nonneg _).trans hRi
    have hb : |caSig Mz e l i| ≤ α i + |R i| := by
      rw [hsplit]
      calc |e i * -α i + R i| ≤ |e i * -α i| + |R i| := abs_add_le _ _
        _ = α i + |R i| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hα0]; rcases hei with h | h <;> simp [h]
    refine ⟨gap_back _ _ hei ?_ ?_, hb⟩
    · rw [hsplit]
      rcases hei with h | h <;> rw [h] <;> linarith [neg_abs_le (R i), le_abs_self (R i)]
    · linarith [abs_nonneg (R i)]
  obtain ⟨c, hc⟩ := hne
  by_cases htwo : ∃ c', c' ≠ c ∧ e c' ≠ 0
  · obtain ⟨c', hc'c, hc'⟩ := htwo
    obtain ⟨g1, b1⟩ := hgap c hc
    obtain ⟨g2, b2⟩ := hgap c' hc'
    have hR1 := hR c; have hR2 := hR c'; have hA1 := hαA c; have hA2 := hαA c'
    have hle := Finset.add_le_sum (f := fun i => ((gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) : ℕ) : ℤ) ^ 2)
      (fun i _ => sq_nonneg _) (mem_univ c) (mem_univ c') hc'c.symm
    rw [g1, g2] at hle
    have hx : (p : ℤ) - 2 * A - 1 ≤ p - |caSig Mz e l c| - 1 := by linarith
    have hy : (p : ℤ) - 2 * A - 1 ≤ p - |caSig Mz e l c'| - 1 := by linarith
    have h0 : (0 : ℤ) ≤ p - 2 * A - 1 := by linarith
    nlinarith [mul_le_mul hx hx h0 (h0.trans hx), mul_le_mul hy hy h0 (h0.trans hy)]
  · simp only [not_exists, not_and, not_not] at htwo
    obtain ⟨g1, -⟩ := hgap c hc
    have hRc : R c = 0 := Finset.sum_eq_zero fun c' hc' => by
      rw [htwo c' (ne_of_mem_erase hc'), zero_mul]
    have hσc : |caSig Mz e l c| ≤ A := by
      rw [hsplit, hRc, add_zero]
      have hec : e c = 1 ∨ e c = -1 := by have := he c; omega
      have hα0 : 0 ≤ α c := (abs_nonneg _).trans (hR c)
      rcases hec with h | h <;> rw [h] <;> simp [abs_of_nonneg hα0, hαA c]
    have hle := Finset.single_le_sum (f := fun i => ((gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) : ℕ) : ℤ) ^ 2)
      (fun i _ => sq_nonneg _) (mem_univ c)
    rw [g1] at hle
    have hx : (p : ℤ) - A - 1 ≤ p - |caSig Mz e l c| - 1 := by linarith
    have h0 : (0 : ℤ) ≤ p - A - 1 := by linarith
    nlinarith [mul_le_mul hx hx h0 (h0.trans hx)]

end Dom

/-! ## Soundness of the checker `caCheck` -/

section Check

lemma allFold_sound {σ β : Type} (f : σ → β → σ) (leaf : σ → Bool) :
    ∀ (n : ℕ) (O : Fin n → List β) (st : σ), allFold f leaf (List.ofFn O) st = true →
      ∀ x : Fin n → β, (∀ k, x k ∈ O k) → leaf ((List.ofFn x).foldl f st) = true
  | 0, O, st, h, x, _ => by simpa [allFold] using h
  | n + 1, O, st, h, x, hx => by
    rw [List.ofFn_succ, allFold, List.all_eq_true] at h
    rw [List.ofFn_succ, List.foldl_cons]
    exact allFold_sound f leaf n _ _ (h (x 0) (hx 0)) _ fun k => hx k.succ

lemma foldl_add_eq {M : Type*} [AddMonoid M] : ∀ (l : List M) (a : M), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | b :: l, a => by rw [List.foldl_cons, foldl_add_eq l, List.sum_cons, add_assoc]

/-- Decoding the packed leaf state: base-`4` codes and base-`256` digits. -/
lemma caLeafSum_decode (p : ℕ) : ∀ (k : ℕ) (a d : Fin k → ℕ), (∀ i, a i < 4) → (∀ i, d i < 256) →
    caLeafSum p k (∑ i, a i * 4 ^ (i : ℕ)) (∑ i, d i * 256 ^ (i : ℕ)) = ∑ i, caGap p (a i) (d i) ^ 2
  | 0, a, d, _, _ => by simp [caLeafSum]
  | k + 1, a, d, ha, hd => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    have e1 : ∑ i : Fin k, a i.succ * (4 ^ (i : ℕ) * 4) = 4 * ∑ i : Fin k, a i.succ * 4 ^ (i : ℕ) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    have e2 : ∑ i : Fin k, d i.succ * (256 ^ (i : ℕ) * 256) = 256 * ∑ i : Fin k, d i.succ * 256 ^ (i : ℕ) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [e1, e2, caLeafSum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hd 0), Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (ha 0),
      Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hd 0), zero_add, zero_add,
      caLeafSum_decode p k _ _ (fun i => ha _) (fun i => hd _)]
    simp [sq]

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- The code of a step coordinate: `0, 1, 2` for `e = 0, 1, -1`. -/
def caCode (e : ℤ) : ℕ := if e = 0 then 0 else if e = 1 then 1 else 2

/-- `caGap` is the one-digit numerator `f_1(e, σ) · p` (`gapNum1`) for `e ∈ {-1, 0, 1}` and the packed digit
`d = 64 + σ`. -/
lemma caGap_eq (e σ : ℤ) (he : e = 0 ∨ e = 1 ∨ e = -1) (d : ℕ) (hd : (d : ℤ) = 64 + σ) :
    caGap p (caCode e) d = gapNum1 p e (σ : ZMod p) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hrv : (d + (p - 1) * 64) % p = (σ : ZMod p).val := by
    have h1 : ((σ : ZMod p).val : ℤ) = σ % p := ZMod.val_intCast σ
    have h2 : ((d + (p - 1) * 64 : ℕ) : ℤ) = σ + p * 64 := by
      push_cast [Nat.cast_sub hp1]; rw [hd]; ring
    have h3 : (((d + (p - 1) * 64) % p : ℕ) : ℤ) = σ % p := by
      rw [Int.natCast_mod, h2, Int.add_mul_emod_self_left]
    omega
  have hrp : (σ : ZMod p).val < p := ZMod.val_lt _
  unfold caGap
  rw [hrv]
  by_cases h0 : (σ : ZMod p) = 0
  · rw [h0, gapNum1_zero, ZMod.val_zero]
    rcases he with rfl | rfl | rfl <;> simp [caCode]
  · have hr0 : (σ : ZMod p).val ≠ 0 := (ZMod.val_ne_zero _).mpr h0
    rw [gapNum1_eq p e _ h0]
    generalize (σ : ZMod p).val = r at hr0 hrp ⊢
    rcases he with rfl | rfl | rfl <;> simp [caCode, hr0] <;> omega

/-- **Soundness of the checker** (`thm:block`(c), "Small primes"): if `caCheck s opts st0 p A` evaluates to `true` (with
the literal options equal to `caOpts` of the partial sums `M^{(j)}`, all `|σ_i| ≤ 63`), then every step has a term
`≥ 1 - (A+1)/p`, i.e. the one-digit relaxation `LB(F) ≥ 1 - (A+1)/p` at this prime. -/
theorem caCheck_sound (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (Bd : Fin s → Fin s → ℤ) (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (hB63 : ∀ i, ∑ c, Bd i c ≤ 63)
    (opts : List (List (ℤ × ℤ))) (hopts : opts = List.ofFn fun k => caOpts Mz (Fin.rev k))
    (st0 : ℤ) (hst0 : st0 = caStart s) (A : ℕ) (hA : A + 1 ≤ p) (hchk : caCheck s opts st0 p A = true)
    (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2) := by
  rintro e l ⟨he, hne, hl⟩
  simp_rw [sig_cast hs Fz Mz hM e l (fun c => (hl c).1)]
  apply LB_of_sq
  have hjj2 : ∀ c, min (l c) (s - 1) - 1 + 2 ≤ s := fun c => by have := (hl c).1; omega
  have he3 : ∀ c, e c = 0 ∨ e c = 1 ∨ e c = -1 := fun c => by have := he c; omega
  have hσb : ∀ i, |caSig Mz e l i| ≤ 63 := by
    intro i
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun c _ => ?_).trans (hB63 i))
    rw [abs_mul]
    have h1 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
    have h2 := hB _ (hjj2 c) i c
    nlinarith [abs_nonneg (e c), abs_nonneg (Mz (min (l c) (s - 1) - 1) i c)]
  set x : Fin s → ℤ × ℤ := fun c => ((caCode (e c) : ℤ) * 4 ^ (c : ℕ),
    e c * caCol (Mz (min (l c) (s - 1) - 1)) c) with hx
  have hxmem : ∀ k, x (Fin.rev k) ∈ caOpts Mz (Fin.rev k) := by
    intro k
    generalize Fin.rev k = c
    rcases he3 c with h | h | h
    · simp [hx, h, caCode, caOpts]
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨min (l c) (s - 1) - 1, List.mem_range.mpr (by have := hjj2 c; omega), by simp [hx, h, caCode]⟩))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨min (l c) (s - 1) - 1, List.mem_range.mpr (by have := hjj2 c; omega), by simp [hx, h, caCode]⟩))
  have hleaf := allFold_sound (· + ·) (caLeaf s p A) s (fun k => caOpts Mz (Fin.rev k)) (0, st0)
    (by rw [← hopts]; exact hchk) (fun k => x (Fin.rev k)) hxmem
  rw [foldl_add_eq, List.sum_ofFn] at hleaf
  have hsum : ∑ k, x (Fin.rev k) = ∑ c, x c := Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [hsum] at hleaf
  have hdig : ∀ i, (((64 + caSig Mz e l i).toNat : ℕ) : ℤ) = 64 + caSig Mz e l i := fun i =>
    Int.toNat_of_nonneg (by have := abs_le.mp (hσb i); linarith)
  have h1 : ((0, st0) + ∑ c, x c).1 = ((∑ c, caCode (e c) * 4 ^ (c : ℕ) : ℕ) : ℤ) := by
    simp [Prod.fst_sum, hx]
  have h2 : ((0, st0) + ∑ c, x c).2 = ((∑ i, (64 + caSig Mz e l i).toNat * 256 ^ (i : ℕ) : ℕ) : ℤ) := by
    rw [Prod.snd_add, Prod.snd_sum, hst0]
    push_cast
    simp only [hdig]
    simp only [hx, caStart, caSig, caCol, add_mul, sum_add_distrib, sum_mul, mul_sum]
    rw [Finset.sum_comm (f := fun x i => e x * (Mz (min (l x) (s - 1) - 1) i x * 256 ^ (i : ℕ)))]
    exact congrArg _ (sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring)
  unfold caLeaf at hleaf
  rw [h1, h2] at hleaf
  have hne0 : ((∑ c, caCode (e c) * 4 ^ (c : ℕ) : ℕ) : ℤ) ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    have hcode : 1 ≤ caCode (e c) := by unfold caCode; split_ifs <;> simp_all
    have h3 := Finset.single_le_sum (f := fun c => caCode (e c) * 4 ^ (c : ℕ)) (fun _ _ => Nat.zero_le _)
      (mem_univ c)
    have h4 : 1 ≤ 4 ^ (c : ℕ) := Nat.one_le_pow _ _ (by norm_num)
    have h5 : 1 ≤ ∑ c, caCode (e c) * 4 ^ (c : ℕ) := le_trans (by nlinarith) h3
    omega
  simp only [Int.toNat_natCast] at hleaf
  rw [Bool.or_eq_true, beq_iff_eq, Nat.ble_eq] at hleaf
  replace hleaf := hleaf.resolve_left hne0
  rw [caLeafSum_decode p s _ _ (fun i => by unfold caCode; split_ifs <;> omega)
    (fun i => by have := hdig i; have := abs_le.mp (hσb i); omega)] at hleaf
  have hg : ∀ i, caGap p (caCode (e i)) (64 + caSig Mz e l i).toNat =
      gapNum1 p (e i) ((caSig Mz e l i : ℤ) : ZMod p) := fun i => caGap_eq _ _ (he3 i) _ (hdig i)
  simp only [hg] at hleaf
  have hT : (((p - A - 1 : ℕ) : ℤ)) = (p : ℤ) - A - 1 := by omega
  rw [← hT]
  exact_mod_cast hleaf

end Check

end GeoSeq
