/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Gap
public import GeoSeq.V94WF

@[expose] public section

/-!
# GeoSeq stage V9-6 (part 4): `thm:block`(a), (b)

* `cert_back1`, `cert_back3`: the term of a step is `≥ 1 - 2/p` if one moving coordinate is backward with `|σ| ≤ 1`, or
  (three coordinates) if all three are backward with `|σ| ≤ 2` (`√3 (1 - 3/p) ≥ 1 - 2/p` for `p ≥ 5`).
* `blk2_good`, `blk3_good` (finite case checks by `decide`: all steps, and for `s = 3` all carry-length patterns):
  every step has such coordinates (the sign analysis of `thm:block`(a), (b)).
* **`blk2_block`** (`thm:block`(a)): for every prime `p ≥ 3` and `θ ≠ 0` the sequence is a digital `(0,2)`-sequence, the
  design relation holds at every `P_{4K}`, and `sep(P_{4K}) ≥ 1 - 2/p`.
* **`blk3_block`** (`thm:block`(b)): for every prime `p ≥ 5`, a digital `(0,3)`-sequence with the design relation at every
  `P_{9K}` and `sep(P_{9K}) ≥ 1 - 2/p`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

lemma decode3 (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) :
    ∃ e' : Fin s → Fin 3, ∀ c, e c = ((e' c : ℕ) : ℤ) - 1 :=
  ⟨fun c => ⟨(e c + 1).toNat, by have := he c; omega⟩, fun c => by
    simp only; have := he c; omega⟩

/-- One backward moving coordinate with `|σ| ≤ 1` gives a term `≥ 1 - 2/p`. -/
lemma cert_back1 (hp : 3 ≤ p) (e : Fin s → ℤ) (σ : Fin s → ℤ) (i : Fin s) (hei : e i = 1 ∨ e i = -1)
    (het : e i * σ i ≤ 0) (hσ : |σ i| ≤ 1) :
    ((p : ℝ) - 2) / p ≤ Real.sqrt (∑ j, ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hg := gap_back (p := p) (e i) (σ i) hei het (by omega)
  have hgR : ((gapNum1 p (e i) (σ i : ZMod p) : ℕ) : ℝ) = (p : ℝ) - |(σ i : ℝ)| - 1 := by
    have : ((gapNum1 p (e i) (σ i : ZMod p) : ℕ) : ℤ) = p - |σ i| - 1 := hg
    have h2 : (((gapNum1 p (e i) (σ i : ZMod p) : ℕ) : ℤ) : ℝ) = ((p - |σ i| - 1 : ℤ) : ℝ) := by rw [this]
    push_cast at h2; exact h2
  have habs : |(σ i : ℝ)| ≤ 1 := by exact_mod_cast hσ
  have hterm : ((p : ℝ) - 2) / p ≤ (gapNum1 p (e i) (σ i : ZMod p) : ℝ) / p := by
    rw [hgR]; exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hnn : (0 : ℝ) ≤ (gapNum1 p (e i) (σ i : ZMod p) : ℝ) / p := by positivity
  calc ((p : ℝ) - 2) / p ≤ (gapNum1 p (e i) (σ i : ZMod p) : ℝ) / p := hterm
    _ = Real.sqrt (((gapNum1 p (e i) (σ i : ZMod p) : ℝ) / p) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
        (f := fun j => ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2) (fun j _ => sq_nonneg _) (mem_univ i))

/-- Three backward coordinates with `|σ| ≤ 2` give a term `≥ √3 (1 - 3/p) ≥ 1 - 2/p` (`p ≥ 5`). -/
lemma cert_back3 (hp : 5 ≤ p) (e : Fin 3 → ℤ) (σ : Fin 3 → ℤ)
    (h : ∀ i, (e i = 1 ∨ e i = -1) ∧ e i * σ i ≤ 0 ∧ |σ i| ≤ 2) :
    ((p : ℝ) - 2) / p ≤ Real.sqrt (∑ j, ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hterm : ∀ j, ((p : ℝ) - 3) / p ≤ (gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p := by
    intro j
    obtain ⟨hej, het, hσ⟩ := h j
    have hg := gap_back (p := p) (e j) (σ j) hej het (by omega)
    have h2 : (((gapNum1 p (e j) (σ j : ZMod p) : ℕ) : ℤ) : ℝ) = ((p - |σ j| - 1 : ℤ) : ℝ) := by rw [hg]
    push_cast at h2
    have habs : |(σ j : ℝ)| ≤ 2 := by exact_mod_cast hσ
    rw [h2]
    exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hsq : ∀ j, (((p : ℝ) - 3) / p) ^ 2 ≤ ((gapNum1 p (e j) (σ j : ZMod p) : ℝ) / p) ^ 2 := fun j =>
    pow_le_pow_left₀ (div_nonneg (by linarith) hp0.le) (hterm j) 2
  apply Real.le_sqrt_of_sq_le
  rw [Fin.sum_univ_three]
  have h1 := hsq 0; have h2 := hsq 1; have h3 := hsq 2
  have key : (((p : ℝ) - 2) / p) ^ 2 ≤ 3 * (((p : ℝ) - 3) / p) ^ 2 := by
    rw [div_pow, div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  linarith

/-! ## `thm:block`(a) -/

/-- **The sign analysis of `thm:block`(a)** (exhaustive over the 8 steps, `decide`): every step has a backward moving
coordinate with `|σ| ≤ 1`. -/
theorem blk2_good : ∀ e' : Fin 2 → Fin 3, (∃ c, e' c ≠ 1) →
    ∃ i, (dec3 e' i = 1 ∨ dec3 e' i = -1) ∧ dec3 e' i * blk2sig (dec3 e') i ≤ 0 ∧
      |blk2sig (dec3 e') i| ≤ 1 := by
  decide

lemma blk2_hNd (c : Fin 2) (n : ℕ) (hn : n + 2 ≤ 2) :
    ∃ N', blk2N (p := p) c (2 - 1 - n) = (X - C (faurePl c)) ^ n * N' ∧ N'.eval (faurePl c) ≠ 0 := by
  obtain rfl : n = 0 := by omega
  refine ⟨blk2N c 1, by simp, ?_⟩
  unfold blk2N; split_ifs <;> simp

lemma blk2_hrel (c i : Fin 2) (h : i ≠ c) :
    wCoCo (faurePl : Fin 2 → ZMod p) c i = -C ((1 : Fin 2 → ZMod p) i) *
      ∑ n ∈ range (2 - 1), C (blockF blk2F n i c) * blk2N c (2 - 1 - n) := by
  fin_cases c <;> fin_cases i
  · exact absurd rfl h
  · simp [wCoCo, blockF, blk2F, blk2N, show (univ.erase (0 : Fin 2)).erase 1 = ∅ by decide]
  · simp [wCoCo, blockF, blk2F, blk2N, show (univ.erase (1 : Fin 2)).erase 0 = ∅ by decide]
  · exact absurd rfl h

/-- **`thm:block`(a)**: `s = 2`, places `(0, 1)`, `v = (1, 1)`, `F_0 = ((-1,1),(-1,-1))`. For every prime `p ≥ 3` and
`θ ≠ 0` the sequence is a digital `(0,2)`-sequence, at every full level `P_{4K}` the geometric digits follow the design
exactly, and `sep(P_{4K}) ≥ 1 - 2/p` for every `K ≥ 1`. -/
theorem blk2_block (hp : 3 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk2 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (2 * (2 * K)) →
        seqDigit (zcode p) (blk2 θ) x i (2 * K) =
          ∑ c, ∑ n ∈ range (2 - 1), blockF blk2F n i c * seqDigit (zcode p) (blk2 θ) x c (2 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 2 (2 * K) (seqPoint (zcode p) (blk2 θ)) (((p : ℝ) - 2) / p) := by
  have ha := faurePl_injective_two (p := p)
  have hv : ∀ c, (1 : Fin 2 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  refine ⟨blockGen_t0 θ 2 1 _ blk2N 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv blk2_hNd,
    fun K hK i x hx => blockGen_rel_seq faurePl θ 2 1 _ blk2N 1 (zcode p) ha hθ le_rfl (by norm_num)
      blk2_hrel hv K hK i x hx, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 2) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have h := block_sep faurePl ha θ hθ 2 le_rfl le_rfl 1 hv (blockF blk2F) blk2N 1 hv blk2_hNd blk2_hrel K hK
    (((p : ℝ) - 2) / p) ?_
  · rwa [min_eq_right hLB1] at h
  rintro e l ⟨he, hne, hl⟩
  have hσ : ∀ i, (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (2 - 1)), blockF blk2F n i c') =
      ((blk2sig e i : ℤ) : ZMod p) := by
    intro i
    unfold blk2sig
    push_cast
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [show min (l c') (2 - 1) = 1 by have := hl c'; omega, Finset.sum_range_one]
    rfl
  simp_rw [hσ]
  obtain ⟨e', he'⟩ := decode3 e he
  have hfun : dec3 e' = e := funext fun c => (he' c).symm
  obtain ⟨i, hi⟩ := blk2_good e' (by
    obtain ⟨c, hc⟩ := hne
    exact ⟨c, fun h => hc (by rw [he' c, h]; rfl)⟩)
  have hi' : (e i = 1 ∨ e i = -1) ∧ e i * blk2sig e i ≤ 0 ∧ |blk2sig e i| ≤ 1 := by rw [← hfun]; exact hi
  exact cert_back1 hp e (blk2sig e) i hi'.1 hi'.2.1 hi'.2.2

/-! ## `thm:block`(b) -/

lemma blk3a_injective (hp : 3 ≤ p) : Function.Injective (blk3a (p := p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two (by omega)
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h21 : (2 : ZMod p) ≠ 1 := fun h => h1 (by linear_combination h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [blk3a]

lemma blk3v_ne (hp : 3 ≤ p) (c : Fin 3) : blk3v (p := p) c ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two (by omega)
  fin_cases c
  · simp [blk3v, h2]
  · simp [blk3v, h2]
  · show (-1 : ZMod p) ≠ 0
    have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)

lemma blk3_hNd (hp : 3 ≤ p) (c : Fin 3) (n : ℕ) (hn : n + 2 ≤ 3) :
    ∃ N', blk3N (p := p) c (3 - 1 - n) = (X - C (blk3a c)) ^ n * N' ∧ N'.eval (blk3a c) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · refine ⟨blk3N c 2, by simp, ?_⟩
    fin_cases c <;> norm_num [blk3N, blk3a, h2]
  · fin_cases c
    · exact ⟨1, by simp [blk3N, blk3a], by simp⟩
    · exact ⟨1, by simp [blk3N, blk3a], by simp⟩
    · refine ⟨C 4, ?_, by simp [h4]⟩
      simp only [blk3N, blk3a]
      simp; ring

lemma blk3_hrel (hp : 3 ≤ p) (c i : Fin 3) (h : i ≠ c) :
    wCoCo (blk3a (p := p)) c i = -C (blk3v i) *
      ∑ n ∈ range (3 - 1), C (blockF blk3F n i c) * blk3N c (3 - 1 - n) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two (by omega)
  have hC : (C (2 : ZMod p)⁻¹ : (ZMod p)[X]) * 2 = 1 := by
    rw [show (2 : (ZMod p)[X]) = C 2 from (map_ofNat C 2).symm, ← map_mul, inv_mul_cancel₀ h2, map_one]
  have h2' : (C (2 : ZMod p) : (ZMod p)[X]) = 2 := map_ofNat C 2
  have h4' : (C (4 : ZMod p) : (ZMod p)[X]) = 4 := map_ofNat C 4
  have hm : (C (-1 : ZMod p) : (ZMod p)[X]) = -1 := (map_neg C (1 : ZMod p)).trans (by rw [map_one])
  fin_cases c <;> fin_cases i <;>
    simp [wCoCo, blockF, blk3F, blk3N, blk3v, blk3a, Finset.sum_range_succ,
      show (univ.erase (0 : Fin 3)).erase 1 = {2} by decide, show (univ.erase (0 : Fin 3)).erase 2 = {1} by decide,
      show (univ.erase (1 : Fin 3)).erase 0 = {2} by decide, show (univ.erase (1 : Fin 3)).erase 2 = {0} by decide,
      show (univ.erase (2 : Fin 3)).erase 0 = {1} by decide, show (univ.erase (2 : Fin 3)).erase 1 = {0} by decide]
    at h ⊢ <;>
    first
    | linear_combination (-(X - 1)) * hC + C (2 : ZMod p)⁻¹ * h2'
    | linear_combination (X - C 2) * hm
    | linear_combination (-(X - 1)) * hC - (X - 1) * C (2 : ZMod p)⁻¹ * h2'
    | linear_combination (X * (C 2 - 1)) * hm - X * h2'
    | linear_combination (-(X - 2)) * hC + (C (2 : ZMod p)⁻¹ * X - 1) * h2' + (C (2 : ZMod p)⁻¹ * (1 - X)) * h4'
    | linear_combination (-X) * hC - (C (2 : ZMod p)⁻¹ * X) * h2'

/-- **The sign analysis of `thm:block`(b)** (exhaustive over the 26 steps and the 8 carry-length patterns, `decide`):
every step has a backward moving coordinate with `|σ| ≤ 1`, or all three coordinates are backward with `|σ| ≤ 2`. -/
theorem blk3_good : ∀ e' : Fin 3 → Fin 3, ∀ ω : Fin 3 → Bool, (∃ c, e' c ≠ 1) →
    (∃ i, (dec3 e' i = 1 ∨ dec3 e' i = -1) ∧ dec3 e' i * blk3sig (dec3 e') ω i ≤ 0 ∧
        |blk3sig (dec3 e') ω i| ≤ 1) ∨
      (∀ i, (dec3 e' i = 1 ∨ dec3 e' i = -1) ∧ dec3 e' i * blk3sig (dec3 e') ω i ≤ 0 ∧
        |blk3sig (dec3 e') ω i| ≤ 2) := by
  decide

/-- **`thm:block`(b)**: `s = 3`, places `(0, 2, 1)`, `v = (1/2, 1/2, -1)`, `(F_0, F_1) = (M, J)`. For every prime
`p ≥ 5` and `θ ≠ 0` the sequence is a digital `(0,3)`-sequence, at every full level `P_{9K}` the geometric digits follow
the design exactly, and `sep(P_{9K}) ≥ 1 - 2/p` for every `K ≥ 1`. -/
theorem blk3_block (hp : 5 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk3 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (3 * (3 * K)) →
        seqDigit (zcode p) (blk3 θ) x i (3 * K) =
          ∑ c, ∑ n ∈ range (3 - 1), blockF blk3F n i c * seqDigit (zcode p) (blk3 θ) x c (3 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 3 (3 * K) (seqPoint (zcode p) (blk3 θ)) (((p : ℝ) - 2) / p) := by
  have ha := blk3a_injective (p := p) (by omega)
  have hv := blk3v_ne (p := p) (by omega)
  have hv1 : ∀ c, (1 : Fin 3 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := blk3_hNd (p := p) (by omega)
  have hrel := blk3_hrel (p := p) (by omega)
  refine ⟨blockGen_t0 θ 3 blk3v _ blk3N 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq blk3a θ 3 blk3v _ blk3N 1 (zcode p) ha hθ le_rfl (by norm_num)
      hrel hv K hK i x hx, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 2) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have h := block_sep blk3a ha θ hθ 3 le_rfl (by norm_num) blk3v hv (blockF blk3F) blk3N 1 hv1 hNd hrel K hK
    (((p : ℝ) - 2) / p) ?_
  · rwa [min_eq_right hLB1] at h
  rintro e l ⟨he, hne, hl⟩
  set ω : Fin 3 → Bool := fun c => decide (2 ≤ l c) with hω
  have hσ : ∀ i, (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (3 - 1)), blockF blk3F n i c') =
      ((blk3sig e ω i : ℤ) : ZMod p) := by
    intro i
    unfold blk3sig
    push_cast
    refine Finset.sum_congr rfl fun c' _ => ?_
    congr 1
    by_cases h2 : 2 ≤ l c'
    · rw [show min (l c') (3 - 1) = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one]
      simp [hω, h2, blockF]
    · rw [show min (l c') (3 - 1) = 1 by have := hl c'; omega, Finset.sum_range_one]
      simp [hω, h2, blockF]
  simp_rw [hσ]
  obtain ⟨e', he'⟩ := decode3 e he
  have hfun : dec3 e' = e := funext fun c => (he' c).symm
  have hgood := blk3_good e' ω (by
    obtain ⟨c, hc⟩ := hne
    exact ⟨c, fun h => hc (by rw [he' c, h]; rfl)⟩)
  have hgood' : (∃ i, (e i = 1 ∨ e i = -1) ∧ e i * blk3sig e ω i ≤ 0 ∧ |blk3sig e ω i| ≤ 1) ∨
      (∀ i, (e i = 1 ∨ e i = -1) ∧ e i * blk3sig e ω i ≤ 0 ∧ |blk3sig e ω i| ≤ 2) := by
    rw [← hfun]; exact hgood
  rcases hgood' with ⟨i, hi⟩ | hall
  · exact cert_back1 (by omega) e (blk3sig e ω) i hi.1 hi.2.1 hi.2.2
  · exact cert_back3 hp e (blk3sig e ω) hall

end GeoSeq
