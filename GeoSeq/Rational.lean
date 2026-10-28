/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S10: rational power series and the irrationality of local roots (`prop:N2`)

* Closure of `IsRatPS` under `+`, `-`, `·`, constants, polynomials and division by a nonzero rational
  series; `isRat_partial` (`f` is rational iff its partial-sum series `f/(1-x)` is).
* `evPeriodic_isRat`: an eventually periodic coefficient sequence gives a rational series.
* **`no_rat_root`** (proof of `prop:N2`): if `w` is monic of degree `s ≥ 2` and `θ ≠ 0`, no power series
  `z` with `w(z) = θx` is rational. Degree argument: from `Q z = P` one gets the polynomial identity
  `∑_i w_i P^i Q^{s-i} = θ x Q^s`, whose two sides have degrees `s·deg P` resp. `≤ s·deg Q` on the left
  and `1 + s·deg Q` on the right (the irreducibility of `w(Z) - y` in the paper, in elementary form).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

lemma coe_ne_zero_of_ne {Q : F[X]} (h : Q ≠ 0) : (Q : PS) ≠ 0 := by
  rwa [Ne, Polynomial.coe_eq_zero_iff]

lemma isRat_coe (P : F[X]) : IsRatPS (P : PS) := ⟨P, 1, one_ne_zero, by simp⟩

lemma isRat_C (a : F) : IsRatPS (PowerSeries.C a : PS) := by
  simpa using isRat_coe (Polynomial.C a)

lemma IsRatPS.add {f g : PS} (hf : IsRatPS f) (hg : IsRatPS g) : IsRatPS (f + g) := by
  obtain ⟨P1, Q1, h1, e1⟩ := hf
  obtain ⟨P2, Q2, h2, e2⟩ := hg
  refine ⟨P1 * Q2 + P2 * Q1, Q1 * Q2, mul_ne_zero h1 h2, ?_⟩
  push_cast
  rw [← e1, ← e2]; ring

lemma IsRatPS.mul {f g : PS} (hf : IsRatPS f) (hg : IsRatPS g) : IsRatPS (f * g) := by
  obtain ⟨P1, Q1, h1, e1⟩ := hf
  obtain ⟨P2, Q2, h2, e2⟩ := hg
  refine ⟨P1 * P2, Q1 * Q2, mul_ne_zero h1 h2, ?_⟩
  push_cast
  rw [← e1, ← e2]; ring

lemma IsRatPS.neg {f : PS} (hf : IsRatPS f) : IsRatPS (-f) := by
  obtain ⟨P, Q, h, e⟩ := hf
  exact ⟨-P, Q, h, by push_cast; rw [← e]; ring⟩

lemma IsRatPS.sub {f g : PS} (hf : IsRatPS f) (hg : IsRatPS g) : IsRatPS (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- Division: if `g h = f` with `f`, `g` rational and `g ≠ 0`, then `h` is rational. -/
lemma IsRatPS.of_mul_left {f g h : PS} (hf : IsRatPS f) (hg : IsRatPS g) (hg0 : g ≠ 0)
    (e : g * h = f) : IsRatPS h := by
  obtain ⟨P1, Q1, h1, e1⟩ := hf
  obtain ⟨P2, Q2, h2, e2⟩ := hg
  have hP2 : P2 ≠ 0 := by
    rintro rfl
    simp only [Polynomial.coe_zero] at e2
    exact hg0 ((mul_eq_zero.1 e2).resolve_left (coe_ne_zero_of_ne h2))
  refine ⟨Q2 * P1, Q1 * P2, mul_ne_zero h1 hP2, ?_⟩
  push_cast
  rw [← e1, ← e2, ← e]; ring

lemma isRat_mk_one : IsRatPS (PowerSeries.mk 1 : PS) :=
  ⟨1, 1 - Polynomial.X, by
    intro h
    have := congrArg (Polynomial.coeff · 1) h
    simp [Polynomial.coeff_one] at this, by
    push_cast
    rw [mul_comm]
    exact PowerSeries.mk_one_mul_one_sub_eq_one F⟩

/-- `f` is rational iff its partial-sum series `f/(1-x)` is. -/
lemma isRat_partial (f : PS) : IsRatPS (f * PowerSeries.mk 1) ↔ IsRatPS f := by
  constructor
  · intro h
    have e : f * PowerSeries.mk 1 * (1 - X) = f := by
      rw [mul_assoc, PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]
    have h1X : IsRatPS ((1 : PS) - X) := by
      have := isRat_coe ((1 : F[X]) - Polynomial.X)
      rwa [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X] at this
    rw [← e]
    exact h.mul h1X
  · intro h; exact h.mul isRat_mk_one

/-- An eventually periodic coefficient sequence gives a rational series. -/
lemma evPeriodic_isRat (a : ℕ → F) (h : EvPeriodic a) : IsRatPS (PowerSeries.mk a) := by
  obtain ⟨N, T, hT, hper⟩ := h
  refine ⟨PowerSeries.trunc (N + T) ((1 - X ^ T) * PowerSeries.mk a), 1 - Polynomial.X ^ T, ?_, ?_⟩
  · intro h0
    have := congrArg (Polynomial.coeff · 0) h0
    simp [Polynomial.coeff_X_pow, show ¬ (0 = T) by omega] at this
  · push_cast
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
        PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have := hper (n - T) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      rw [this, sub_self]

/-- `Q^s · w(z) = ∑_{i ≤ s} w_i (Qz)^i Q^{s-i}`. -/
lemma homog_eval (w : F[X]) (z Qs : PS) :
    Qs ^ w.natDegree * Polynomial.aeval z w =
      ∑ i ∈ range (w.natDegree + 1),
        PowerSeries.C (w.coeff i) * (Qs * z) ^ i * Qs ^ (w.natDegree - i) := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [PowerSeries.smul_eq_C_mul, mul_pow]
  have : Qs ^ w.natDegree = Qs ^ i * Qs ^ (w.natDegree - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [this]
  ring

/-- **The local roots are irrational** (proof of `prop:N2`): if `w` is monic of degree `≥ 2` and
`θ ≠ 0`, no power series `z` with `w(z) = θx` is rational. -/
theorem no_rat_root (w : F[X]) (hw : w.Monic) (hs : 2 ≤ w.natDegree) (θ : F) (hθ : θ ≠ 0)
    (z : PS) (hz : Polynomial.aeval z w = PowerSeries.C θ * X) : ¬ IsRatPS z := by
  rintro ⟨P, Q, hQ, hQz⟩
  set s := w.natDegree with hsdef
  set L : F[X] := ∑ i ∈ range (s + 1), Polynomial.C (w.coeff i) * P ^ i * Q ^ (s - i) with hL
  have hLeq : L = Polynomial.C θ * Polynomial.X * Q ^ s := by
    apply Polynomial.coe_injective
    have h1 := homog_eval w z (Q : PS)
    rw [hz, hQz, ← hsdef] at h1
    rw [hL, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_pow]
    rw [← h1]; ring
  obtain ⟨dP, hdP⟩ : ∃ d, P.natDegree = d := ⟨_, rfl⟩
  obtain ⟨dQ, hdQ⟩ : ∃ d, Q.natDegree = d := ⟨_, rfl⟩
  have hR : (Polynomial.C θ * Polynomial.X * Q ^ s).natDegree = s * dQ + 1 := by
    rw [Polynomial.natDegree_mul (by simp [hθ]) (pow_ne_zero _ hQ), Polynomial.natDegree_C_mul_X _ hθ,
      Polynomial.natDegree_pow, hdQ]
    ring
  have hterm : ∀ i ∈ range (s + 1),
      (Polynomial.C (w.coeff i) * P ^ i * Q ^ (s - i)).natDegree ≤ i * dP + (s - i) * dQ := by
    intro i _
    refine (Polynomial.natDegree_mul_le).trans ?_
    refine add_le_add ((Polynomial.natDegree_C_mul_le _ _).trans ?_) ?_
    · exact Polynomial.natDegree_pow_le.trans (by rw [hdP])
    · exact Polynomial.natDegree_pow_le.trans (by rw [hdQ])
  rcases le_or_gt dP dQ with hPQ | hPQ
  · have hle : L.natDegree ≤ s * dQ := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => (hterm i hi).trans ?_
      have hi' : i ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      calc i * dP + (s - i) * dQ ≤ i * dQ + (s - i) * dQ := by gcongr
        _ = s * dQ := by rw [← add_mul, Nat.add_sub_cancel' hi']
    rw [hLeq, hR] at hle
    omega
  · have hsplit : L = P ^ s + ∑ i ∈ range s, Polynomial.C (w.coeff i) * P ^ i * Q ^ (s - i) := by
      rw [hL, Finset.sum_range_succ, add_comm]
      congr 1
      have : w.coeff s = 1 := hw
      simp [this]
    have hlt : ∀ i ∈ range s, i * dP + (s - i) * dQ ≤ (s - 1) * dP + dQ := by
      intro i hi
      have hi' : i < s := Finset.mem_range.1 hi
      obtain ⟨k, hk⟩ : ∃ k, s - i = k + 1 := ⟨s - i - 1, by omega⟩
      have hk' : s - 1 = i + k := by omega
      rw [hk, hk']
      nlinarith [Nat.mul_le_mul_left k hPQ.le]
    have hb : (∑ i ∈ range s, Polynomial.C (w.coeff i) * P ^ i * Q ^ (s - i)).natDegree ≤
        (s - 1) * dP + dQ :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (hterm i (Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega))).trans (hlt i hi)
    have hsd : s * dP = (s - 1) * dP + dP := by
      obtain ⟨t, ht⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rw [ht, Nat.add_sub_cancel]; ring
    have hrest : (∑ i ∈ range s, Polynomial.C (w.coeff i) * P ^ i * Q ^ (s - i)).natDegree <
        (P ^ s).natDegree := by
      rw [Polynomial.natDegree_pow, hdP]
      omega
    have hdeg : L.natDegree = s * dP := by
      rw [hsplit, Polynomial.natDegree_add_eq_left_of_natDegree_lt hrest, Polynomial.natDegree_pow, hdP]
    rw [hLeq, hR] at hdeg
    have : s * (dQ + 1) ≤ s * dP := Nat.mul_le_mul_left _ hPQ
    rw [Nat.mul_add, mul_one] at this
    omega

end GeoSeq
