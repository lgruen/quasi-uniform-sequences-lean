/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.OneDigit
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S10: `lem:H` (the symmetric barrier)

Residues are represented by `ZMod.valMinAbs` (in `(-p/2, p/2)` for odd `p`).

* `g1_vma`, `g0_vma`: the one-digit gaps `f_1(1, σ)`, `f_1(0, σ)` (numerators `gapNum1`) through the centred
  representative: `p + σ̄ - 1` for `σ̄ ≤ 0`, `σ̄ - 1` for `σ̄ > 0`; `max(0, |σ̄| - 1)`.
* **`lemH_core`**: the integer form of `lem:H` — from the three certificate terms with `l_0 = l_1 = l`
  (axis, diagonal, antidiagonal), `-(k-1) ≤ Ō ≤ 0` and `|X̄| ≤ -Ō`.
* **`lemH`**: the statement of the paper: a symmetric law (`symLaw`) whose certificate (`lem:cert`, `j = 1`)
  has value `≥ 1 - k/p` at level `K` satisfies the bounds for every `1 ≤ l ≤ K`.
-/

namespace GeoSeq

open Finset

section

variable (p : ℕ) [Fact p.Prime]

lemma vma_val (σ : ZMod p) (hσ : σ ≠ 0) :
    (σ.valMinAbs ≤ 0 → σ.valMinAbs = σ.val - p) ∧ (0 < σ.valMinAbs → σ.valMinAbs = σ.val) := by
  rw [ZMod.valMinAbs_def_pos]
  have hv : 0 < σ.val := by rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hσ
  split_ifs with h
  · exact ⟨fun h' => by omega, fun _ => rfl⟩
  · exact ⟨fun _ => rfl, fun h' => by have := ZMod.val_lt σ; omega⟩

/-- `f_1(1, σ)`: numerator `p + σ̄ - 1` (`σ̄ ≤ 0`) or `σ̄ - 1` (`σ̄ > 0`). -/
lemma g1_vma (σ : ZMod p) :
    (gapNum1 p 1 σ : ℤ) = if σ.valMinAbs ≤ 0 then p + σ.valMinAbs - 1 else σ.valMinAbs - 1 := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hσ : σ = 0
  · subst hσ
    rw [gapNum1_zero]; simp; omega
  · obtain ⟨h1, h2⟩ := vma_val p σ hσ
    have hv : 0 < σ.val := by rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hσ
    rw [gapNum1_eq p 1 σ hσ]
    have e1 : ((1 : ℤ) * p + σ.val).natAbs = p + σ.val := by omega
    have e2 : ((1 : ℤ) * p + σ.val - p).natAbs = σ.val := by omega
    rw [e1, e2, min_eq_right (by omega)]
    split_ifs with h
    · rw [h1 h]; push_cast [Nat.cast_sub (show 1 ≤ σ.val by omega)]; ring
    · rw [h2 (by omega)]; push_cast [Nat.cast_sub (show 1 ≤ σ.val by omega)]; ring

/-- `f_1(0, σ)`: numerator `max(0, |σ̄| - 1)`. -/
lemma g0_vma (σ : ZMod p) : (gapNum1 p 0 σ : ℤ) = max 0 (|σ.valMinAbs| - 1) := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hσ : σ = 0
  · subst hσ; rw [gapNum1_zero]; simp
  · obtain ⟨h1, h2⟩ := vma_val p σ hσ
    have hv : 0 < σ.val := by rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hσ
    have hvl := ZMod.val_lt σ
    rw [gapNum1_eq p 0 σ hσ]
    have e1 : ((0 : ℤ) * p + σ.val).natAbs = σ.val := by omega
    have e2 : ((0 : ℤ) * p + σ.val - p).natAbs = p - σ.val := by omega
    rw [e1, e2]
    rcases le_or_gt σ.valMinAbs 0 with h | h
    · have := h1 h
      rw [abs_of_nonpos h, this]
      have hm : min σ.val (p - σ.val) = p - σ.val := by
        have := σ.valMinAbs_mem_Ioc; simp only [Set.mem_Ioc] at this; omega
      rw [hm]; omega
    · have := h2 h
      rw [abs_of_pos h, this]
      have hm : min σ.val (p - σ.val) = σ.val := by
        have := σ.valMinAbs_mem_Ioc; simp only [Set.mem_Ioc] at this; omega
      rw [hm]; omega

lemma vma_bound (σ : ZMod p) : 2 * |σ.valMinAbs| ≤ p := by
  have := σ.valMinAbs_mem_Ioc; simp only [Set.mem_Ioc] at this
  rcases abs_cases σ.valMinAbs with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

end

lemma sq_le_sq_of {a b : ℤ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha h 2

lemma four_sq {a b : ℤ} (ha : 0 ≤ a) (h : 2 * a ≤ b) : 4 * a ^ 2 ≤ b ^ 2 := by
  have := sq_le_sq_of (by linarith) h; linarith [show (2 * a) ^ 2 = 4 * a ^ 2 by ring]

lemma scaled_sq {a b : ℤ} (c d : ℤ) (ha : 0 ≤ c * a) (h : c * a ≤ d * b) :
    c ^ 2 * a ^ 2 ≤ d ^ 2 * b ^ 2 := by
  have := sq_le_sq_of ha h; rw [mul_pow, mul_pow] at this; exact this

/-- **`lem:H`, integer core**: let `p ≥ 11` be prime, `1 ≤ k`, `10k ≤ p`, `k² + 2 < 2p`. If the axis, diagonal
and antidiagonal certificate terms (numerators, `l_0 = l_1 = l`) of a symmetric law with responses
`O = O^{(l)}`, `X = X^{(l)}` are at least `(p - k)²`, then `-(k-1) ≤ Ō ≤ 0` and `|X̄| ≤ -Ō`. -/
theorem lemH_core (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (k : ℕ) (hk1 : 1 ≤ k) (hk : 10 * k ≤ p)
    (hk2 : k ^ 2 + 2 < 2 * p) (O X : ZMod p)
    (hax : ((p : ℤ) - k) ^ 2 ≤ (gapNum1 p 1 O : ℤ) ^ 2 + (gapNum1 p 0 X : ℤ) ^ 2)
    (hdi : ((p : ℤ) - k) ^ 2 ≤ 2 * (gapNum1 p 1 (O + X) : ℤ) ^ 2)
    (han : ((p : ℤ) - k) ^ 2 ≤ 2 * (gapNum1 p 1 (O - X) : ℤ) ^ 2) :
    -((k : ℤ) - 1) ≤ O.valMinAbs ∧ O.valMinAbs ≤ 0 ∧ |X.valMinAbs| ≤ -O.valMinAbs := by
  have hP : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
  have hpk : 9 * (p : ℤ) ≤ 10 * ((p : ℤ) - k) := by push_cast; omega
  have hpk2 : 81 * (p : ℤ) ^ 2 ≤ 100 * ((p : ℤ) - k) ^ 2 := by
    have := scaled_sq 9 10 (by positivity) hpk; linarith
  have bx := vma_bound p X
  have bo := vma_bound p O
  have hxa := abs_le.1 (show |X.valMinAbs| ≤ |X.valMinAbs| from le_rfl)
  -- the cross gap on the axis is below `p/2`
  have hg0 : 2 * (gapNum1 p 0 X : ℤ) ≤ p := by
    rw [g0_vma]; rcases le_total 0 (|X.valMinAbs| - 1) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; positivity
  have hg0sq : 4 * (gapNum1 p 0 X : ℤ) ^ 2 ≤ (p : ℤ) ^ 2 := four_sq (Int.natCast_nonneg _) hg0
  -- Step 1: `Ō ≤ 0` and `50 Ō > -13 p`
  have hg1 := g1_vma p O
  have ho0 : O.valMinAbs ≤ 0 := by
    by_contra h
    rw [if_neg h] at hg1
    have h2 : 2 * (gapNum1 p 1 O : ℤ) ≤ p := by
      rw [hg1]; have := abs_of_pos (lt_of_not_ge h); linarith
    have h4 := four_sq (Int.natCast_nonneg _) h2
    linarith
  rw [if_pos ho0] at hg1
  have ho13 : -13 * (p : ℤ) < 50 * O.valMinAbs := by
    have hge : 0 ≤ (p : ℤ) + O.valMinAbs - 1 := by rw [← hg1]; exact Int.natCast_nonneg _
    by_contra h
    push_neg at h
    have h1 : 50 * ((p : ℤ) + O.valMinAbs - 1) ≤ 37 * p := by linarith
    have h2 := scaled_sq 50 37 (by positivity) h1
    rw [hg1] at hax
    norm_num at h2
    linarith
  -- Step 2: the diagonal and antidiagonal sums are `≤ 0` and `> -0.37 p`
  have diag : ∀ σ : ZMod p, ((p : ℤ) - k) ^ 2 ≤ 2 * (gapNum1 p 1 σ : ℤ) ^ 2 →
      σ.valMinAbs ≤ 0 ∧ -37 * (p : ℤ) < 100 * σ.valMinAbs := by
    intro σ hs
    have bs := vma_bound p σ
    have hgs := g1_vma p σ
    have hs0 : σ.valMinAbs ≤ 0 := by
      by_contra h
      rw [if_neg h] at hgs
      have h2 : 2 * (gapNum1 p 1 σ : ℤ) ≤ p := by
        rw [hgs]; have := abs_of_pos (lt_of_not_ge h); linarith
      have h4 := four_sq (Int.natCast_nonneg _) h2
      linarith
    refine ⟨hs0, ?_⟩
    rw [if_pos hs0] at hgs
    have hge : 0 ≤ (p : ℤ) + σ.valMinAbs - 1 := by rw [← hgs]; exact Int.natCast_nonneg _
    by_contra h
    push_neg at h
    have h1 : 100 * ((p : ℤ) + σ.valMinAbs - 1) ≤ 63 * p := by linarith
    have h2 := scaled_sq 100 63 (by positivity) h1
    rw [hgs] at hs
    norm_num at h2
    linarith
  have same : ∀ (σ : ZMod p) (t : ℤ), (t : ZMod p) = σ → -(p : ℤ) < t - σ.valMinAbs →
      t - σ.valMinAbs < p → t = σ.valMinAbs := by
    intro σ t ht h1 h2
    have hd : ((t - σ.valMinAbs : ℤ) : ZMod p) = 0 := by
      push_cast; rw [ht]; simp
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  obtain ⟨hd0, hd37⟩ := diag (O + X) hdi
  obtain ⟨ha0, ha37⟩ := diag (O - X) han
  have hxl : -(p : ℤ) ≤ 2 * X.valMinAbs ∧ 2 * X.valMinAbs ≤ p := by
    rcases abs_cases X.valMinAbs with ⟨h, _⟩ | ⟨h, _⟩ <;> constructor <;> linarith
  have hox : O.valMinAbs + X.valMinAbs = (O + X).valMinAbs :=
    same (O + X) _ (by simp)
      (by linarith) (by linarith)
  have hoxm : O.valMinAbs - X.valMinAbs = (O - X).valMinAbs :=
    same (O - X) _ (by simp)
      (by linarith) (by linarith)
  have hxo : |X.valMinAbs| ≤ -O.valMinAbs := by
    rw [abs_le]; constructor <;> linarith
  -- Step 3: `-Ō ≤ k - 1`
  refine ⟨?_, ho0, hxo⟩
  by_contra hA
  push_neg at hA
  have hg0' : (gapNum1 p 0 X : ℤ) ≤ -O.valMinAbs - 1 := by
    rw [g0_vma]; exact max_le (by linarith) (by linarith)
  have hsq := sq_le_sq_of (Int.natCast_nonneg _) hg0'
  rw [hg1] at hax
  have hid : ((p : ℤ) + O.valMinAbs - 1) ^ 2 + (-O.valMinAbs - 1) ^ 2 -
      (((p : ℤ) - k - 1) ^ 2 + ((k : ℤ) - 1) ^ 2) =
        2 * (-O.valMinAbs - k) * (-O.valMinAbs + k - p) := by ring
  have h1 : 0 ≤ -O.valMinAbs - k := by linarith
  have h2 : -O.valMinAbs + k - p ≤ 0 := by push_cast; linarith
  have hprod : 2 * (-O.valMinAbs - k) * (-O.valMinAbs + k - p) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos h1 h2; linarith
  have hf : ((p : ℤ) - k - 1) ^ 2 + ((k : ℤ) - 1) ^ 2 = ((p : ℤ) - k) ^ 2 - 2 * p + (k : ℤ) ^ 2 + 2 := by
    ring
  have hk2' : ((k : ℤ)) ^ 2 + 2 < 2 * p := by exact_mod_cast hk2
  linarith

section NoFact

/-- `σ` of `lem:cert` (`j = 1`) for the symmetric law and a step `(e_0, e_1)` with equal carry lengths. -/
lemma sym_sig (p : ℕ) (Ol Xl : ℕ → ZMod p) (l : ℕ) (e0 e1 : ℤ) :
    certSigmaP (symLaw Ol Xl) 1 ![e0, e1] (fun _ => l) 0 0 =
        (e0 : ZMod p) * Ol l + (e1 : ZMod p) * Xl l ∧
      certSigmaP (symLaw Ol Xl) 1 ![e0, e1] (fun _ => l) 1 0 =
        (e0 : ZMod p) * Xl l + (e1 : ZMod p) * Ol l := by
  simp [certSigmaP, symLaw, Fin.sum_univ_two]

lemma lin_cast (p : ℕ) (x y : ZMod p) (a b : ℤ) (ha : a = 1) (hb : b = -1) :
    (a : ZMod p) * x + (b : ZMod p) * y = x - y := by
  subst ha hb; push_cast; ring

lemma lin_cast1 (p : ℕ) (x y : ZMod p) (a b : ℤ) (ha : a = 1) (hb : b = 1) :
    (a : ZMod p) * x + (b : ZMod p) * y = x + y := by
  subst ha hb; push_cast; ring

lemma lin_cast0 (p : ℕ) (x y : ZMod p) (a b : ℤ) (ha : a = 1) (hb : b = 0) :
    (a : ZMod p) * x + (b : ZMod p) * y = x := by
  subst ha hb; push_cast; ring

lemma lin_cast0' (p : ℕ) (x y : ZMod p) (a b : ℤ) (ha : a = 1) (hb : b = 0) :
    (a : ZMod p) * y + (b : ZMod p) * x = y := by
  subst ha hb; push_cast; ring

lemma g1_neg_sub (p : ℕ) [NeZero p] (x y : ZMod p) :
    gapNum1 p (-1) (y - x) = gapNum1 p 1 (x - y) := by
  rw [F1_neg, neg_sub]

end NoFact

/-- From a certificate term `≥ (p-k)/p` (`j = 1`, `s = 2`) to the integer inequality on numerators. -/
lemma certTerm_int (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k ≤ p) (e : Fin 2 → ℤ)
    (σ : Fin 2 → Fin 1 → ZMod p) (h : ((p : ℝ) - k) / p ≤ certTerm (zcode p) 1 e σ) :
    ((p : ℤ) - k) ^ 2 ≤ (gapNum1 p (e 0) (σ 0 0) : ℤ) ^ 2 + (gapNum1 p (e 1) (σ 1 0) : ℤ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk' : (k : ℝ) ≤ p := by exact_mod_cast hk
  have hnn : (0 : ℝ) ≤ ((p : ℝ) - k) / p := div_nonneg (by linarith) hp0.le
  rw [certTerm, Real.le_sqrt hnn (by positivity), Fin.sum_univ_two, gapNum_one, gapNum_one, div_pow, div_pow,
    div_pow, pow_one, ← add_div, div_le_div_iff_of_pos_right (by positivity)] at h
  exact_mod_cast h

/-- **`lem:H`** (symmetric barrier): let `p ≥ 11` be prime, `1 ≤ k`, `10k ≤ p` and `k² < 2p - 2`. If a
symmetric law (`O_0^{(l)} = O_1^{(l)} = O^{(l)}`, `X_{0←1}^{(l)} = X_{1←0}^{(l)} = X^{(l)}`) has certificate value
`LB_1 ≥ 1 - k/p` at level `K` (`lem:cert` with `j = 1`: every step term is `≥ 1 - k/p`), then for every
`1 ≤ l ≤ K`: `-(k-1) ≤ O^{(l)} ≤ 0` and `|X^{(l)}| ≤ -O^{(l)}` (centred representatives). -/
theorem lemH (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (k : ℕ) (hk1 : 1 ≤ k) (hk : 10 * k ≤ p)
    (hk2 : k ^ 2 + 2 < 2 * p) (K : ℕ) (Ol Xl : ℕ → ZMod p)
    (hcert : ∀ (e : Fin 2 → ℤ) (l : Fin 2 → ℕ), IsStep K e l →
      ((p : ℝ) - k) / p ≤ certTerm (zcode p) 1 e (certSigmaP (symLaw Ol Xl) 1 e l))
    (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    -((k : ℤ) - 1) ≤ (Ol l).valMinAbs ∧ (Ol l).valMinAbs ≤ 0 ∧
      |(Xl l).valMinAbs| ≤ -(Ol l).valMinAbs := by
  have hkp : k ≤ p := by omega
  have step : ∀ e : Fin 2 → ℤ, (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
      IsStep K e (fun _ => l) := fun e h1 h2 => ⟨h1, h2, fun _ => ⟨hl, hlK⟩⟩
  have hax := certTerm_int p k hkp _ _ (hcert ![1, 0] _ (step _ (by decide) ⟨0, by decide⟩))
  have hdi := certTerm_int p k hkp _ _ (hcert ![1, 1] _ (step _ (by decide) ⟨0, by decide⟩))
  have han := certTerm_int p k hkp _ _ (hcert ![1, -1] _ (step _ (by decide) ⟨0, by decide⟩))
  rw [(sym_sig p Ol Xl l 1 0).1, (sym_sig p Ol Xl l 1 0).2, lin_cast0 p _ _ _ _ rfl rfl,
    lin_cast0' p _ _ _ _ rfl rfl] at hax
  rw [(sym_sig p Ol Xl l 1 1).1, (sym_sig p Ol Xl l 1 1).2, lin_cast1 p _ _ _ _ rfl rfl,
    lin_cast1 p _ _ _ _ rfl rfl, add_comm (Xl l)] at hdi
  rw [(sym_sig p Ol Xl l 1 (-1)).1, (sym_sig p Ol Xl l 1 (-1)).2, lin_cast p _ _ _ _ rfl rfl,
    lin_cast p _ _ _ _ rfl rfl] at han
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hax hdi han
  rw [g1_neg_sub] at han
  exact lemH_core p hp k hk1 hk hk2 (Ol l) (Xl l) hax (by linarith) (by linarith)

end GeoSeq
