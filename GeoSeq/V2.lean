/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2Lex
public import GeoSeq.V2WS
public import GeoSeq.V2Cauchy

@[expose] public section

/-!
# GeoSeq stage V2: mixed-radix designs (`def:MR`, `thm:MR`)

* Arithmetic of (MR1)–(MR3): `mrMu_mul` (`μ_{cj}` is an integer: `μ_{cj} c! (n-j)! (j-c) = n!`), `mrG_dvd`,
  `mrG_pos`, the steps `ν_{tj} ≥ 1`, the window recursion `mrN = wsN` (`mrN_eq_wsN`), and the bounds
  that `Γ < p` gives (`h_t < p`, `p ≥ 5`, all windows are arcs).
* `faure_placeDer`: `w'(c) = (-1)^{n-c} c! (n-c)!` for the Faure frame.
* **`MR_kap`**: the crosses of `MR(s,p,h)` are the integers `κ_{c←j} = (-1)^{n-c} μ̄_{cj} h_{c+1} ⋯ h_j` of (MR2).
* `MR_cond_i`, `MR_cond_ii`: conditions (i), (ii) of `prop:steer` (via `lem:lexcover`, `lem:ws`);
  `MR_LB` (`LB(W) = (p - Γ)/p`, `lem:lex`, `rem:lexexact`).
* **`MR`** = `thm:MR`; **`MR_every`** (every multiplier family with the constants `λ_c` and responses in the
  windows); **`MR101`** = `ex:MR101` (non-vacuity, `LB = 28/101 > 0`, by `decide +kernel`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Arith

/-- `μ_{cj} c! (n-j)! (j-c) = n!` for `c < j ≤ n = s - 1`: `μ_{cj}` is an integer (`def:MR`). -/
theorem mrMu_mul (s c j : ℕ) (hcj : c < j) (hj : j ≤ s - 1) :
    mrMu s c j * (c.factorial * (s - 1 - j).factorial * (j - c)) = (s - 1).factorial := by
  unfold mrMu
  apply Nat.div_mul_cancel
  have h1 : c.factorial * (j - c).factorial ∣ j.factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add c (j - c)
    rwa [Nat.add_sub_cancel' hcj.le] at this
  have h2 : j.factorial * (s - 1 - j).factorial ∣ (s - 1).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add j (s - 1 - j)
    rwa [Nat.add_sub_cancel' hj] at this
  have h3 : (j - c) ∣ (j - c).factorial := Nat.dvd_factorial (by omega) le_rfl
  calc c.factorial * (s - 1 - j).factorial * (j - c)
      ∣ c.factorial * (s - 1 - j).factorial * (j - c).factorial := Nat.mul_dvd_mul_left _ h3
    _ = c.factorial * (j - c).factorial * (s - 1 - j).factorial := by ring
    _ ∣ j.factorial * (s - 1 - j).factorial := Nat.mul_dvd_mul_right h1 _
    _ ∣ (s - 1).factorial := h2

theorem mrMu_pos (s c j : ℕ) (hcj : c < j) (hj : j ≤ s - 1) : 1 ≤ mrMu s c j := by
  have := mrMu_mul s c j hcj hj
  rcases Nat.eq_zero_or_pos (mrMu s c j) with h | h
  · rw [h, zero_mul] at this; exact absurd this.symm (Nat.factorial_ne_zero _)
  · exact h

theorem mrG_dvd (s c j : ℕ) (hcj : c < j) (hj : j < s) : mrG s ∣ mrMu s c j := by
  unfold mrG
  exact Finset.gcd_dvd (f := fun x : ℕ × ℕ => mrMu s x.1 x.2) (b := (c, j))
    (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr hj⟩, hcj⟩)

theorem mrG_pos (s : ℕ) (hs : 2 ≤ s) : 0 < mrG s := by
  rcases Nat.eq_zero_or_pos (mrG s) with h | h
  · have := mrG_dvd s 0 1 (by omega) (by omega)
    rw [h, zero_dvd_iff] at this
    have := mrMu_pos s 0 1 (by omega) (by omega)
    omega
  · exact h

theorem mrG_dvd_fact (s : ℕ) (hs : 2 ≤ s) : mrG s ∣ (s - 1).factorial :=
  (mrG_dvd s 0 1 (by omega) (by omega)).trans (Dvd.intro _ (mrMu_mul s 0 1 (by omega) (by omega)))

/-- `μ̄_{cj} (n-j)! c! (j-c) = n!/gcd` (both sides times `gcd` are `n!`). -/
theorem mrMuBar_mul (s c j : ℕ) (hs : 2 ≤ s) (hcj : c < j) (hj : j < s) :
    mrMu s c j / mrG s * ((s - 1 - j).factorial * c.factorial * (j - c)) =
      (s - 1).factorial / mrG s := by
  have hg := mrG_pos s hs
  apply Nat.eq_of_mul_eq_mul_right hg
  rw [Nat.div_mul_cancel (mrG_dvd_fact s hs)]
  have e := mrMu_mul s c j hcj (by omega)
  calc mrMu s c j / mrG s * ((s - 1 - j).factorial * c.factorial * (j - c)) * mrG s
      = mrMu s c j / mrG s * mrG s * (c.factorial * (s - 1 - j).factorial * (j - c)) := by ring
    _ = (s - 1).factorial := by rw [Nat.div_mul_cancel (mrG_dvd s c j hcj hj), e]

theorem mrMuBar_pos (s c j : ℕ) (hs : 2 ≤ s) (hcj : c < j) (hj : j < s) : 1 ≤ mrMu s c j / mrG s := by
  have h1 := mrMu_pos s c j hcj (by omega)
  have h2 := mrG_dvd s c j hcj hj
  have h3 := mrG_pos s hs
  obtain ⟨k, hk⟩ := h2
  rw [hk, Nat.mul_div_cancel_left _ h3]
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, mul_zero] at hk; omega
  · exact h

lemma hprod_pos (h : ℕ → ℕ) (a b : ℕ) (hh : ∀ i, a < i → i ≤ b → 1 ≤ h i) : 1 ≤ hprod h a b := by
  unfold hprod
  exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i hi => by
    have := hh i (mem_Ioc.mp hi).1 (mem_Ioc.mp hi).2; omega)

lemma hprod_split (h : ℕ → ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    hprod h a b * hprod h b c = hprod h a c := by
  unfold hprod
  exact Finset.prod_Ioc_consecutive _ hab hbc

lemma hprod_le (h : ℕ → ℕ) (t : ℕ) (ht : 1 ≤ t) : h t ≤ hprod h (t - 1) t := by
  unfold hprod
  have : Ioc (t - 1) t = {t} := by ext i; simp; omega
  rw [this, prod_singleton]

theorem mrNu_pos (s : ℕ) (hs : 2 ≤ s) (h : ℕ → ℕ) (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t)
    (t j : ℕ) (htj : t < j) (hj : j < s) : 1 ≤ mrNu s h t j := by
  unfold mrNu
  exact Nat.mul_le_mul (mrMuBar_pos s t j hs htj hj) (hprod_pos h t j fun i h1 h2 => hh i (by omega) (by omega))

end Arith

section Faure

lemma prod_range_sub_self (c : ℕ) : ∏ b ∈ range c, ((c : ℤ) - b) = c.factorial := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [prod_range_succ', Nat.factorial_succ]
    push_cast
    have : ∏ x ∈ range c, ((c : ℤ) + 1 - ((x : ℤ) + 1)) = ∏ x ∈ range c, ((c : ℤ) - x) :=
      prod_congr rfl fun _ _ => by ring
    rw [this, ih]; ring

/-- `∏_{b<s, b≠c} (c - b) = (-1)^{s-1-c} c! (s-1-c)!` over `ℤ`. -/
lemma prod_range_erase_sub (c s : ℕ) (hc : c < s) :
    ∏ b ∈ (range s).erase c, ((c : ℤ) - b) = (-1) ^ (s - 1 - c) * c.factorial * (s - 1 - c).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, s = c + 1 + k := ⟨s - c - 1, by omega⟩
  induction k with
  | zero =>
    rw [show c + 1 + 0 = c + 1 from rfl, range_add_one, erase_insert (by simp), prod_range_sub_self]
    simp
  | succ k ih =>
    rw [show c + 1 + (k + 1) = (c + 1 + k) + 1 by ring, range_add_one,
      erase_insert_of_ne (by omega), prod_insert (by simp), ih (by omega)]
    rw [show c + 1 + k + 1 - 1 - c = (c + 1 + k - 1 - c) + 1 by omega, pow_succ, Nat.factorial_succ]
    push_cast
    rw [show ((c + 1 + k - 1 - c : ℕ) : ℤ) = (k : ℤ) by omega]
    ring

/-- **`w'(c) = (-1)^{n-c} c! (n-c)!`** for the Faure frame (places `a_b = b`, `b < s`, `n = s - 1`). -/
theorem faure_placeDer (s p : ℕ) [Fact p.Prime] (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) (c : Fin s) :
    placeDer zθ c =
      (((-1) ^ (s - 1 - c) * (c : ℕ).factorial * (s - 1 - c).factorial : ℤ) : ZMod p) := by
  rw [← prod_range_erase_sub c s c.isLt]
  push_cast
  unfold placeDer ssPlace
  simp only [hplace]
  set f : ℕ → ZMod p := fun b => if b = (c : ℕ) then 1 else ((c : ℕ) : ZMod p) - b
  have h1 : ∏ b ∈ univ.erase c, (((c : ℕ) : ZMod p) - ((b : ℕ) : ZMod p)) =
      ∏ b : Fin s, f b := by
    rw [← Finset.mul_prod_erase univ (fun b : Fin s => f b) (mem_univ c)]
    simp only [f, if_pos rfl, one_mul]
    exact prod_congr rfl fun b hb => by
      rw [if_neg (fun e => (ne_of_mem_erase hb) (Fin.ext e))]
  have h2 : ∏ b ∈ (range s).erase c, (((c : ℕ) : ZMod p) - (b : ZMod p)) = ∏ b ∈ range s, f b := by
    rw [← Finset.mul_prod_erase (range s) f (mem_range.mpr c.isLt)]
    simp only [f, if_pos rfl, one_mul]
    exact prod_congr rfl fun b hb => by rw [if_neg (ne_of_mem_erase hb)]
  rw [h1, h2, Fin.prod_univ_eq_prod_range f s]

end Faure

section Bounds

variable {s p : ℕ} {h : ℕ → ℕ}

lemma mrCost_ge (c : ℕ) (hc : c < s) : 2 * mrB s p h c + mrM s p h c ≤ mrCost s p h :=
  Finset.le_sup (f := fun c => 2 * mrB s p h c + mrM s p h c) (mem_range.mpr hc)

lemma mrBx_le_mrB (c j : ℕ) (hcj : c < j) (hj : j < s) : mrBx s p h c j ≤ mrB s p h c :=
  Finset.single_le_sum (f := fun j => mrBx s p h c j) (fun _ _ => Nat.zero_le _)
    (mem_Ioo.mpr ⟨hcj, hj⟩)

lemma mrNu_le_mrBx (t j : ℕ) : mrNu s h t j ≤ mrBx s p h t j := by
  unfold mrBx
  split_ifs with h0
  · subst h0; exact le_rfl
  · exact le_max_left _ _

lemma mrKapZ_natAbs (t j : ℕ) : (mrKapZ s h t j).natAbs = mrNu s h t j := by
  simp [mrKapZ, Int.natAbs_mul, Int.natAbs_pow]

lemma mrN_eq_wsN (j : ℕ) : ∀ t, mrN s p h j t =
    wsN p (fun t => 2 * mrBx s p h t j + 1) (fun t => mrNu s h t j) t := by
  intro t
  induction t with
  | zero => simp [mrN, wsN, mrBx, Nat.sub_sub]
  | succ t ih => simp only [mrN, wsN, ih]

lemma mrN_pos (hs : 2 ≤ s) (hp : 1 ≤ p) (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (j : ℕ) (hj : j < s) :
    ∀ t, t < j → 1 ≤ mrN s p h j t := by
  intro t
  induction t with
  | zero => intro _; simp [mrN]
  | succ t ih =>
    intro ht
    simp only [mrN]
    have := ih (by omega)
    have := cdiv_pos p _ hp (mrNu_pos s hs h hh (t + 1) j ht hj)
    omega

lemma mrM_pos (hs : 2 ≤ s) (hp : 1 ≤ p) (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (j : ℕ) (hj : j < s) :
    1 ≤ mrM s p h j := by
  unfold mrM
  split_ifs with h0
  · exact le_rfl
  · exact mrN_pos hs hp hh j hj (j - 1) (by omega)

/-- `Γ < p` gives `2B_c + M_c < p`, hence `2 B_{c←j} + 1 < p` and `ν_{cj} < p`. -/
lemma mr_row_lt (hΓ : mrCost s p h < p) (c : ℕ) (hc : c < s) : 2 * mrB s p h c + mrM s p h c < p :=
  lt_of_le_of_lt (mrCost_ge c hc) hΓ

lemma mr_h_lt (hs : 2 ≤ s) (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ s - 1) : h t < p := by
  have hp1 : 1 ≤ p := by have := mrCost_ge (s := s) (p := p) (h := h) 0 (by omega); omega
  have h1 := hprod_le h t ht1
  have h2 := mrMuBar_pos s (t - 1) t hs (by omega) (by omega)
  have h3 : mrNu s h (t - 1) t = mrMu s (t - 1) t / mrG s * hprod h (t - 1) t := rfl
  have h4 := mrNu_le_mrBx (s := s) (p := p) (h := h) (t - 1) t
  have h5 := mrBx_le_mrB (s := s) (p := p) (h := h) (t - 1) t (by omega) (by omega)
  have h6 := mr_row_lt hΓ (t - 1) (by omega)
  have h7 := mrM_pos hs hp1 hh (t - 1) (by omega)
  have : hprod h (t - 1) t ≤ mrNu s h (t - 1) t := by rw [h3]; exact Nat.le_mul_of_pos_left _ h2
  omega

lemma mr_p_ge_five [Fact p.Prime] (hs : 2 ≤ s) (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t)
    (hΓ : mrCost s p h < p) : 5 ≤ p := by
  have h1 := mrNu_pos s hs h hh 0 1 (by omega) (by omega)
  have h2 := mrNu_le_mrBx (s := s) (p := p) (h := h) 0 1
  have h3 := mrBx_le_mrB (s := s) (p := p) (h := h) 0 1 (by omega) (by omega)
  have h4 := mr_row_lt hΓ 0 (by omega)
  have h5 : mrM s p h 0 = 1 := by simp [mrM]
  have hp4 : 4 ≤ p := by omega
  rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
  · subst h; exact absurd (Fact.out : Nat.Prime 4) (by decide)
  · exact h

end Bounds

section Kap

variable {p : ℕ} [Fact p.Prime]

lemma natCast_ne_zero_of_lt {m : ℕ} (h0 : 0 < m) (hm : m < p) : (m : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

lemma factorial_ne_zero_of_lt {m : ℕ} (hm : m < p) : (m.factorial : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd ((Nat.Prime.dvd_factorial Fact.out).mp h) (by omega)

lemma hprod_ne_zero (h : ℕ → ℕ) (a b : ℕ) (hh : ∀ i, a < i → i ≤ b → 1 ≤ h i ∧ h i < p) :
    (hprod h a b : ZMod p) ≠ 0 := by
  unfold hprod
  push_cast
  exact Finset.prod_ne_zero_iff.mpr fun i hi =>
    natCast_ne_zero_of_lt (hh i (mem_Ioc.mp hi).1 (mem_Ioc.mp hi).2).1
      (hh i (mem_Ioc.mp hi).1 (mem_Ioc.mp hi).2).2

/-- **The crosses of `MR(s,p,h)`** (proof of `thm:MR`, "Crosses"): for the Faure frame, the scale
`θ = n!/gcd` and the constants `λ_c = (n-c)!/(h_1 ⋯ h_c)` (`p ≥ s`, step factors `1 ≤ h_t < p`),
`κ_{c←j} = θ λ_c/(λ_j w'(c) (j - c)) = (-1)^{n-c} μ̄_{cj} h_{c+1} ⋯ h_j` for `c < j`, the integers of (MR2). -/
theorem MR_kap (s : ℕ) (hs : 2 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t ∧ h t < p) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) (c j : Fin s) (hcj : c < j) :
    kapL (mrTheta s p) (mrLam s p h) zθ c j = (mrKapZ s h c j : ZMod p) := by
  have hcj' : (c : ℕ) < j := hcj
  have hjs := j.isLt
  have hcs := c.isLt
  have hW := faure_placeDer s p zθ hplace c
  have hΔ : ssPlace zθ j - ssPlace zθ c = (((j : ℕ) - (c : ℕ) : ℕ) : ZMod p) := by
    simp only [ssPlace, hplace]; rw [Nat.cast_sub hcj'.le]
  have hHc := hprod_ne_zero (p := p) h 0 c (fun i h1 h2 => hh i (by omega) (by omega))
  have hHcj := hprod_ne_zero (p := p) h c j (fun i h1 h2 => hh i (by omega) (by omega))
  have hsplit : ((hprod h 0 j : ℕ) : ZMod p) = (hprod h 0 c : ZMod p) * (hprod h c j : ZMod p) := by
    rw [← hprod_split h (Nat.zero_le _) hcj'.le]; push_cast; ring
  have hf1 := factorial_ne_zero_of_lt (p := p) (m := (c : ℕ)) (by omega)
  have hf2 := factorial_ne_zero_of_lt (p := p) (m := s - 1 - (c : ℕ)) (by omega)
  have hf3 := factorial_ne_zero_of_lt (p := p) (m := s - 1 - (j : ℕ)) (by omega)
  have hd := natCast_ne_zero_of_lt (p := p) (m := (j : ℕ) - c) (by omega) (by omega)
  have hkey := congrArg (fun n : ℕ => (n : ZMod p)) (mrMuBar_mul s c j hs hcj' hjs)
  have hsq : (((-1 : ℤ) ^ (s - 1 - (c : ℕ)) : ℤ) : ZMod p) *
      (((-1 : ℤ) ^ (s - 1 - (c : ℕ)) : ℤ) : ZMod p) = 1 := by
    rw [← Int.cast_mul, ← mul_pow]; norm_num
  unfold kapL mrTheta mrLam mrKapZ mrNu
  rw [hW, hΔ, hsplit, ← hkey]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_mul] at hsq ⊢
  field_simp
  rw [sq, hsq, mul_one]

end Kap

section Design

variable {s p : ℕ} {h : ℕ → ℕ}

lemma mrB_eq_lexB (c : Fin s) : lexB (fun c j : Fin s => mrBx s p h c j) c = mrB s p h c := by
  classical
  unfold lexB mrB
  rw [Finset.sum_filter]
  have e : ∀ c' : Fin s, (if c < c' then mrBx s p h c c' else 0) =
      (fun j : ℕ => if (c : ℕ) < j then mrBx s p h c j else 0) c' := fun c' => by
    simp only [Fin.lt_iff_val_lt_val]
  rw [Finset.sum_congr rfl (fun c' _ => e c'),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if (c : ℕ) < j then mrBx s p h c j else 0) s,
    ← Finset.sum_filter]
  congr 1; ext j; simp only [mem_filter, mem_range, mem_Ioo]; omega

lemma mr_lexData (hs : 2 ≤ s) (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p) :
    IsLexData p (fun c : Fin s => mrB s p h c) (fun c => mrM s p h c) (fun c j => mrBx s p h c j) := by
  intro c
  have hp1 : 1 ≤ p := by have := mrCost_ge (s := s) (p := p) (h := h) 0 (by omega); omega
  dsimp only
  rw [mrB_eq_lexB]
  have := mr_row_lt hΓ c c.isLt
  exact ⟨mrM_pos hs hp1 hh c c.isLt, le_rfl, by omega⟩

lemma mr_lexCost : lexCost (fun c : Fin s => mrB s p h c) (fun c => mrM s p h c)
    (fun c j => mrBx s p h c j) = mrCost s p h := by
  have e : lexCost (fun c : Fin s => mrB s p h c) (fun c => mrM s p h c)
      (fun c j => mrBx s p h c j) = univ.sup fun c : Fin s => 2 * mrB s p h c + mrM s p h c := by
    unfold lexCost; congr 1; funext c; rw [mrB_eq_lexB]; ring
  rw [e]
  apply le_antisymm
  · exact Finset.sup_le fun c _ => mrCost_ge (s := s) (p := p) (h := h) c c.isLt
  · exact Finset.sup_le fun c hc =>
      Finset.le_sup (f := fun c : Fin s => 2 * mrB s p h c + mrM s p h c) (mem_univ ⟨c, mem_range.mp hc⟩)

/-- **The window bound of `MR(s,p,h)`** (proof of `thm:MR`, "Bound"; `lem:lex`, `rem:lexexact`): if `Γ < p`,
the windows are ordered and `LB(W) = (p - Γ)/p` (the greatest `LB` with `LB ≤ LB(W)`). -/
theorem MR_LB (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p) :
    IsGreatest {LB : ℝ | WinLB p (mrWin s p h) LB} (((p : ℝ) - mrCost s p h) / p) := by
  have := lex_eq p (Nat.Prime.two_le Fact.out) (by omega) _ _ _ (mr_lexData hs hh hΓ)
  rwa [mr_lexCost] at this

/-- **Condition (i) of `prop:steer`** for `MR(s,p,h)` (`Γ < p`): `-κ_{c←c'} ∈ W_{c←c'}`. -/
theorem MR_cond_i (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p)) (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) :
    ∀ c c' : Fin s, c ≠ c' → -kapL (mrTheta s p) (mrLam s p h) zθ c c' ∈ mrWin s p h c c' := by
  intro c c' hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [MR_kap s hs hsp h (fun t h1 h2 => ⟨hh t h1 h2, mr_h_lt hs hh hΓ t h1 h2⟩) zθ hplace c c' hlt]
    unfold mrWin
    rw [lexWin_up p _ _ _ hlt]
    have hb := mrNu_le_mrBx (s := s) (p := p) (h := h) c c'
    have ha : |mrKapZ s h c c'| = (mrNu s h c c' : ℤ) := by
      rw [Int.abs_eq_natAbs, mrKapZ_natAbs]
    have := abs_le.mp (le_of_eq ha)
    exact ⟨-mrKapZ s h c c', by omega, by omega, by push_cast; rfl⟩
  · unfold mrWin; rw [lexWin_low p _ _ _ hlt]; trivial

/-- **Condition (ii) of `prop:steer`** for `MR(s,p,h)` (`Γ < p`): every column covers (column `0` by
`M_0 = 1`, column `j ≥ 1` by `lem:ws` with row `0` fast and rows `1, …, j-1` slow, and `lem:lexcover`). -/
theorem MR_cond_ii (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p)) (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) :
    ∀ j : Fin s, LinesMeet (stAlpha (mrTheta s p) (mrLam s p h) zθ j) (colWin (mrWin s p h) j) := by
  intro j
  have hp1 : 1 ≤ p := by have := mrCost_ge (s := s) (p := p) (h := h) 0 (by omega); omega
  by_cases hj0 : (j : ℕ) = 0
  · exact lexcover_zero p _ _ zθ _ _ _ j hj0 (by simp [mrM, hj0])
  unfold mrWin
  rw [lexcover_iff _ _ zθ _ j (fun c hc => lexWin_low p _ _ _ hc)]
  intro σ
  have hjs := j.isLt
  have hlen : ∀ t < (j : ℕ), 2 * mrBx s p h t j + 1 ≤ p := by
    intro t ht
    have := mrBx_le_mrB (s := s) (p := p) (h := h) t j ht hjs
    have := mr_row_lt hΓ t (by omega)
    have := mrM_pos hs hp1 hh t (by omega)
    omega
  have hνf : (fun t => (mrKapZ s h t j).natAbs) = fun t => mrNu s h t j := funext fun t => mrKapZ_natAbs t j
  obtain ⟨o, ho1, ho2, hgood⟩ := ws_cover p j (by omega) (fun t => mrKapZ s h t j)
    (fun t => -(mrBx s p h t j : ℤ)) (fun t => 2 * mrBx s p h t j + 1) hlen
    (fun t ht => by rw [mrKapZ_natAbs]; exact mrNu_pos s hs h hh t j ht hjs)
    (by rw [mrKapZ_natAbs]; simp [mrBx]; omega)
    (fun t ht => by
      rw [hνf, ← mrN_eq_wsN, mrKapZ_natAbs]
      have h1 : cdiv (mrN s p h j t * mrNu s h (t + 1) j - 1) 2 ≤ mrBx s p h (t + 1) j := by
        simp only [mrBx, if_neg (Nat.succ_ne_zero t), Nat.add_sub_cancel]; exact le_max_right _ _
      have h2 := cdiv_mul_ge (mrN s p h j t * mrNu s h (t + 1) j - 1) 2 (by norm_num)
      omega)
    (fun t => if ht : t < s then σ ⟨t, ht⟩ else 0) (-((mrB s p h j : ℤ) + mrM s p h j - 1))
  rw [hνf, ← mrN_eq_wsN] at ho2
  have hMj : mrM s p h j = mrN s p h j (j - 1) := by simp [mrM, hj0]
  refine ⟨(o : ZMod p), ?_, fun c hc => ?_⟩
  · rw [lexWin_own]; exact ⟨o, by omega, by omega, rfl⟩
  · rw [lexWin_up p _ _ _ hc, MR_kap s hs hsp h (fun t h1 h2 => ⟨hh t h1 h2, mr_h_lt hs hh hΓ t h1 h2⟩)
      zθ hplace c j hc]
    obtain ⟨i, hi, hx⟩ := hgood c hc
    simp only [dif_pos c.isLt] at hx
    refine ⟨-(mrBx s p h c j : ℤ) + i, by omega, by omega, ?_⟩
    rw [hx]

end Design

section Main

lemma mr_inj (s p : ℕ) [Fact p.Prime] (hsp : s ≤ p) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) : Function.Injective (ssPlace zθ) := by
  intro a b hab
  simp only [ssPlace, hplace] at hab
  exact Fin.ext (natCast_inj_lt p (by omega) (by omega) hab)

lemma mrTheta_ne (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hsp : s ≤ p) : mrTheta s p ≠ 0 := by
  intro h0
  have e := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.div_mul_cancel (mrG_dvd_fact s hs))
  simp only [Nat.cast_mul] at e
  unfold mrTheta at h0
  rw [h0, zero_mul] at e
  exact factorial_ne_zero_of_lt (p := p) (m := s - 1) (by omega) e.symm

lemma mrLam_ne (s p : ℕ) [Fact p.Prime] (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t ∧ h t < p) (c : Fin s) : mrLam s p h c ≠ 0 := by
  have := c.isLt
  unfold mrLam
  exact div_ne_zero (factorial_ne_zero_of_lt (by omega))
    (hprod_ne_zero h 0 c fun i h1 h2 => hh i (by omega) (by omega))

/-- **`thm:MR`** (mixed-radix designs). Let `s ≥ 3`, `p ≥ s` prime, `h_1, …, h_n` positive integers
(`n = s - 1`), `MR(s,p,h)` the mixed-radix design of `def:MR` (Faure frame with local roots `z_c(θx)`,
`w(z_c(θx)) = θx`, `z_c(0) = c`; scale `θ = n!/gcd`; constants `λ_c = (n-c)!/(h_1 ⋯ h_c)`; the ordered
windows of (MR2), (MR3)) and `Γ` its cost. If `Γ < p`, then selection rules exist, and every selection rule
for `MR(s,p,h)` defines a digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every
`K ≥ 1`, and the sequence is quasi-uniform: `h(P_{[N]}) ≤ (√s p/((p - Γ)/p)) δ(P_{[N]})` for every `N ≥ 2`
(`lem:prefix`). -/
theorem MR (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (faureW s p) = C (mrTheta s p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (mrTheta s p) (mrLam s p h) zθ (mrWin s p h) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (mrTheta s p) (mrLam s p h) zθ (mrWin s p h) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ))
        (((p : ℝ) - mrCost s p h) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - mrCost s p h) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p)
                (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ)))) := by
  have hs2 : 2 ≤ s := by omega
  have hp5 := mr_p_ge_five (s := s) (p := p) (h := h) hs2 hh hΓ
  have hhp : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t ∧ h t < p :=
    fun t h1 h2 => ⟨hh t h1 h2, mr_h_lt hs2 hh hΓ t h1 h2⟩
  have hinj := mr_inj s p hsp zθ hplace
  obtain ⟨-, ⟨rule, hrule⟩, hall⟩ := steer p hp5 (faureW s p) (faureW_monic s p) (faureW_natDegree s p)
    (mrTheta s p) (mrTheta_ne s p hs2 hsp) zθ hroot hinj (mrLam s p h) (mrLam_ne s p hsp h hhp)
    (mrWin s p h) (MR_cond_i s p hs2 hsp h hh hΓ zθ hplace) (MR_cond_ii s p hs2 hsp h hh hΓ zθ hplace)
  refine ⟨⟨rule, hrule⟩, fun rule' hrule' => ?_⟩
  obtain ⟨-, hseq, -, hcert⟩ := hall rule' hrule'
  have hLB := (MR_LB s p hs2 h hh hΓ).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hΓR : (mrCost s p h : ℝ) < p := by exact_mod_cast hΓ
  have hpos : (0 : ℝ) < ((p : ℝ) - mrCost s p h) / p := div_pos (by linarith) hpR
  have hle1 : ((p : ℝ) - mrCost s p h) / p ≤ 1 := by
    rw [div_le_one hpR]; have : (0 : ℝ) ≤ mrCost s p h := Nat.cast_nonneg _; linarith
  have hsep : ∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
      (seqPoint (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule') zθ))
      (((p : ℝ) - mrCost s p h) / p) := by
    intro K hK
    have := (hcert _ hLB K hK).2
    rwa [min_eq_right hle1] at this
  exact ⟨hseq, hsep, fun N hN => prefix_mesh (zcode p) _ (by omega) (by omega) hseq _ hpos hsep N hN⟩

/-- **`thm:MR` for every multiplier family** (`prop:steer`, "every selection rule"): under the
hypotheses of `MR`, every self-similar scramble of the Faure frame with the constants `λ_c` of (MR1)
(`g_c(0) ≠ 0`, `λ_c = g_c(0) w'(c)`) whose one-digit responses all lie in the windows of `MR(s,p,h)`
gives a quasi-uniform digital `(0,s)`-sequence with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem MR_every (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (faureW s p) = C (mrTheta s p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p))
    (g : Fin s → PowerSeries (ZMod p)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hlam : ∀ c, lam g zθ c = mrLam s p h c) (hW : RespInS (ssGen g zθ) (mrWin s p h)) :
    IsSeq0 (zcode p) (ssGen g zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
        (((p : ℝ) - mrCost s p h) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - mrCost s p h) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  have hs2 : 2 ≤ s := by omega
  obtain ⟨rule, hrule, hg'⟩ := steer_every p (faureW s p) (faureW_monic s p) (faureW_natDegree s p)
    (mrTheta s p) (mrTheta_ne s p hs2 hsp) zθ hroot (mr_inj s p hsp zθ hplace) (mrLam s p h) (mrWin s p h)
    (MR_cond_ii s p hs2 hsp h hh hΓ zθ hplace) g hg hlam hW
  have := (MR s p hs hsp h hh hΓ zθ hroot hplace).2 rule hrule
  rwa [hg'] at this

end Main

end GeoSeq
