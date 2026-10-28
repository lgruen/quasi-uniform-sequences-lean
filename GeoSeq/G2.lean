/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Steer

@[expose] public section

/-!
# GeoSeq stage S7: square-root windows (`cor:G2` = `thm:G`, `app:G2`)

* `cover_round`: every integer `S ∈ [b·lo - b, b·hi + b]` is `b i - ξ` with `i ∈ [lo, hi]`, `|ξ| ≤ b`
  (rounding `S/b` up and clamping: the rounding rule of `app:G2`, with the ceiling in place of the
  nearest integer; `thm:GA` allows every choice).
* `cover_interval`: an integer interval of at least `p` values covers `𝔽_p`.
* `G2_cover`: conditions (i), (ii) of `thm:GA` for `W_x = [-b,b]`, `W_o = [-A,-b]`, `θ = κ = b`.
* `G2_bound`: `min(1 - (A+1)/p, √2(1 - (A+b+1)/p)) > 1 - (2√p+1)/p` for `p ≥ 41`.
* **`G2`** (`cor:G2`).
-/

namespace GeoSeq

open Finset PowerSeries

/-- Every integer `S` with `b lo - b ≤ S ≤ b hi + b` is `b i - ξ` with `lo ≤ i ≤ hi`, `-b ≤ ξ ≤ b`. -/
theorem cover_round (b lo hi S : ℤ) (hb : 1 ≤ b) (hlh : lo ≤ hi) (h1 : b * lo - b ≤ S)
    (h2 : S ≤ b * hi + b) : ∃ i ξ : ℤ, lo ≤ i ∧ i ≤ hi ∧ -b ≤ ξ ∧ ξ ≤ b ∧ S = b * i - ξ := by
  set c := -((-S) / b) with hc
  have hq1 := Int.mul_ediv_self_le (x := -S) (k := b) (by omega)
  have hq2 := Int.lt_mul_ediv_self_add (x := -S) (k := b) (by omega)
  have hc1 : S ≤ b * c := by rw [hc, mul_neg]; linarith
  have hc2 : b * c < S + b := by rw [hc, mul_neg]; linarith
  rcases lt_or_ge c lo with h | h
  · refine ⟨lo, b, le_rfl, hlh, by omega, le_rfl, ?_⟩
    have : b * c ≤ b * (lo - 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith
  · rcases lt_or_ge hi c with h' | h'
    · refine ⟨hi, b * hi - S, hlh, le_rfl, ?_, ?_, by ring⟩
      · linarith
      · have : b * (hi + 1) ≤ b * c := mul_le_mul_of_nonneg_left (by omega) (by omega)
        nlinarith
    · exact ⟨c, b * c - S, h, h', by linarith, by linarith, by ring⟩

/-- An integer interval `[L, L + p - 1]` meets every residue class: every `β ∈ 𝔽_p` is `(S : 𝔽_p)` for some
`S ∈ [L, L + p - 1]`. -/
theorem cover_interval (p : ℕ) [NeZero p] (L : ℤ) (β : ZMod p) :
    ∃ S : ℤ, L ≤ S ∧ S ≤ L + p - 1 ∧ (S : ZMod p) = β := by
  have hp : (0 : ℤ) < p := by exact_mod_cast NeZero.pos p
  refine ⟨L + ((β.val : ℤ) - L) % p, by have := Int.emod_nonneg ((β.val : ℤ) - L) hp.ne'; omega,
    by have := Int.emod_lt_of_pos ((β.val : ℤ) - L) hp; omega, ?_⟩
  rw [Int.cast_add, ZMod.intCast_mod, Int.cast_sub]
  simp

lemma int_neg_nat_cast {R : Type*} [Ring R] (n : ℕ) : ((-(n : ℤ) : ℤ) : R) = -(n : R) := by
  push_cast; rfl

/-- Conditions (i), (ii) of `thm:GA` for the square-root windows (`app:G2`): `-b ∈ [-b, b]` and
`b([-A,-b] - 1) - [-b,b] = 𝔽_p`, for `p ≥ 41`. -/
theorem G2_cover (p : ℕ) [Fact p.Prime] (hp : 41 ≤ p) :
    -((g2b p : ℕ) : ZMod p) ∈ intWin p (-(g2b p : ℤ)) (g2b p) ∧
      Covers ((g2b p : ℕ) : ZMod p) (intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (intWin p (-(g2b p : ℤ)) (g2b p)) := by
  set b := g2b p with hbdef
  have hb1 : 1 ≤ b := by
    rw [hbdef, g2b, Nat.one_le_ceil_iff]; positivity
  set c := (p - 1 + b - 1) / b with hcdef
  have hA : g2A p = b - 2 + c := rfl
  -- `p - 1 ≤ b c`, `c ≥ 2` (from `b ≤ √p + 1 < p - 1`), `b ≥ 2`
  have hbc : p - 1 ≤ b * c := by
    have h1 := Nat.div_add_mod (p - 1 + b - 1) b
    have h2 := Nat.mod_lt (p - 1 + b - 1) (show 0 < b by omega)
    rw [← hcdef] at h1
    omega
  have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt (by positivity)
  have hs6 : (6 : ℝ) ≤ Real.sqrt p := by
    rw [show (6 : ℝ) = Real.sqrt 36 by rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 36 ≤ p by omega))
  have hbR : (b : ℝ) < Real.sqrt p + 1 := Nat.ceil_lt_add_one (by positivity)
  have hbp : b + 3 ≤ p := by
    have : (b : ℝ) + 3 ≤ p := by nlinarith
    exact_mod_cast this
  have hb2 : 2 ≤ b := by
    have : (6 : ℝ) ≤ b := hs6.trans (Nat.le_ceil _)
    have : 6 ≤ b := by exact_mod_cast this
    omega
  have hc2 : 2 ≤ c := by
    rw [hcdef, Nat.le_div_iff_mul_le (by omega)]; omega
  refine ⟨⟨-(b : ℤ), le_rfl, by omega, int_neg_nat_cast b⟩, fun β => ?_⟩
  have hAz : ((b - 2 + c : ℕ) : ℤ) = (b : ℤ) - 2 + c := by omega
  have hbcz : (p : ℤ) - 1 ≤ (b : ℤ) * c := by
    have : ((p - 1 : ℕ) : ℤ) ≤ ((b * c : ℕ) : ℤ) := by exact_mod_cast hbc
    push_cast [show 1 ≤ p by omega] at this
    exact this
  obtain ⟨S, hS1, hS2, hSβ⟩ := cover_interval p (-((b : ℤ) * ((b - 2 + c : ℕ) + 2))) β
  rw [hAz] at hS1 hS2
  obtain ⟨i, ξ, hi1, hi2, hξ1, hξ2, hSi⟩ := cover_round b (-((b - 2 + c : ℕ) : ℤ) - 1) (-(b : ℤ) - 1) S
    (by omega) (by omega) (by rw [hAz]; nlinarith) (by nlinarith)
  refine ⟨((i + 1 : ℤ) : ZMod p), ⟨i + 1, by rw [hA]; omega, by omega, rfl⟩,
    (ξ : ZMod p), ⟨ξ, hξ1, hξ2, rfl⟩, ?_⟩
  rw [← hSβ, hSi]
  push_cast
  ring

/-- The real bound of `cor:G2`: for `p ≥ 41`, `A < 2√p`, `b ≤ A`, `A + b < p`, and
`min(1 - (A+1)/p, √2(1 - (A+b+1)/p)) > 1 - (2√p+1)/p`. -/
theorem G2_bound (p : ℕ) (hp : 41 ≤ p) :
    g2b p ≤ g2A p ∧ g2A p + g2b p < p ∧
      1 - (2 * Real.sqrt p + 1) / p <
        min (1 - ((g2A p : ℝ) + 1) / p) (Real.sqrt 2 * (1 - ((g2A p : ℝ) + g2b p + 1) / p)) := by
  set b := g2b p with hbdef
  set c := (p - 1 + b - 1) / b with hcdef
  have hA : g2A p = b - 2 + c := rfl
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set s := Real.sqrt p with hsdef
  have hsq : s ^ 2 = p := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs64 : (6.4 : ℝ) ≤ s := by
    rw [hsdef, show (6.4 : ℝ) = Real.sqrt (6.4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by have : (41 : ℝ) ≤ p := by exact_mod_cast hp
                                norm_num; linarith)
  have hbR : (b : ℝ) < s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hbs : s ≤ (b : ℝ) := Nat.le_ceil _
  have hb6 : 6 ≤ b := by
    have : (6 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  -- `c b < p - 1 + b`
  have hcb : c * b < p - 1 + b := by
    have h1 := Nat.div_add_mod (p - 1 + b - 1) b
    have h2 := Nat.mod_lt (p - 1 + b - 1) (show 0 < b by omega)
    rw [← hcdef] at h1
    have : b * c ≤ p - 1 + b - 1 := by omega
    rw [mul_comm]; omega
  have hcbR : (c : ℝ) * b < p - 1 + b := by
    have : ((c * b : ℕ) : ℝ) < ((p - 1 + b : ℕ) : ℝ) := by exact_mod_cast hcb
    push_cast [show 1 ≤ p by omega] at this
    exact this
  -- `c < s + 1`
  have hcR : (c : ℝ) < s + 1 := by
    by_contra hcon
    push_neg at hcon
    have : (s + 1) * s ≤ (c : ℝ) * b := mul_le_mul hcon hbs hs0 (by positivity)
    nlinarith
  have hc2 : 2 ≤ c := by
    rw [hcdef, Nat.le_div_iff_mul_le (by omega)]
    have : (b : ℝ) + 3 ≤ p := by nlinarith
    have : b + 3 ≤ p := by exact_mod_cast this
    omega
  have hAR : (g2A p : ℝ) = b - 2 + c := by
    rw [hA]; push_cast [show 2 ≤ b by omega]; ring
  have hA2 : (g2A p : ℝ) < 2 * s := by rw [hAR]; linarith
  refine ⟨by rw [hA]; omega, ?_, lt_min ?_ ?_⟩
  · have : (g2A p : ℝ) + b < p := by nlinarith
    exact_mod_cast this
  · rw [sub_lt_sub_iff_left, div_lt_div_iff_of_pos_right hp0]; linarith
  · -- `√2 (1 - (A+b+1)/p) > √2 (1 - (3s+2)/p) ≥ 1 - (2s+1)/p`
    have h2a : (1.414 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hAb : (g2A p : ℝ) + b + 1 < 3 * s + 2 := by linarith
    have hkey : 1 - (2 * s + 1) / p ≤ Real.sqrt 2 * (1 - (3 * s + 2) / p) := by
      rw [← hsq, one_sub_div (by positivity), one_sub_div (by positivity), mul_div_assoc',
        div_le_div_iff_of_pos_right (by positivity)]
      have hpos : 0 ≤ s ^ 2 - (3 * s + 2) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2a hpos]
    refine lt_of_le_of_lt hkey ?_
    apply mul_lt_mul_of_pos_left _ (by positivity)
    rw [sub_lt_sub_iff_left, div_lt_div_iff_of_pos_right hp0]
    exact hAb

/-- **`cor:G2`** (= `thm:G`, square-root windows): for every prime `p ≥ 41`, with `b = θ = ⌈√p⌉`,
`A = b - 2 + ⌈(p-1)/b⌉`, `W_x = [-b,b]`, `W_o = [-A,-b]` in both columns (symmetric case of `thm:GA`,
`κ_{0←1} = κ_{1←0} = θ`): conditions (i), (ii) hold; a sequence with all responses in the windows
exists; and every such sequence is a `(0,2)`-sequence with `c(P_{2K}) ≥ L` for every `K ≥ 1`, for one
`L > 1 - (2√p+1)/p`. -/
theorem G2 (p : ℕ) [Fact p.Prime] (hp : 41 ≤ p) :
    (-((g2b p : ℕ) : ZMod p) ∈ intWin p (-(g2b p : ℤ)) (g2b p) ∧
      Covers ((g2b p : ℕ) : ZMod p) (intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (intWin p (-(g2b p : ℤ)) (g2b p))) ∧
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      constantCoeff (g 1) = constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (g2b p))) (fun _ => intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (fun _ => intWin p (-(g2b p : ℤ)) (g2b p))) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      constantCoeff (g 1) = constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (g2b p))) (fun _ => intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (fun _ => intWin p (-(g2b p : ℤ)) (g2b p)) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (g2b p))) ∧
        ∃ L : ℝ, 1 - (2 * Real.sqrt p + 1) / p < L ∧
          ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (g2b p)))) L) := by
  have hcov := G2_cover p hp
  obtain ⟨hbA, hAb, hlt⟩ := G2_bound p hp
  set b := g2b p with hbdef
  have hb1 : 1 ≤ b := by
    rw [hbdef, g2b, Nat.one_le_ceil_iff]; positivity
  have hθ : ((b : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hsq : ((b : ℕ) : ZMod p) * ((b : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) ^ 2 := by ring
  have hGA := GA p (by omega) (b : ZMod p) (b : ZMod p) (b : ZMod p) hθ hθ hsq
    (fun _ => intWin p (-(g2A p : ℤ)) (-(b : ℤ))) (fun _ => intWin p (-(b : ℤ)) b)
    hcov.1 hcov.1 hcov.2 hcov.2
  refine ⟨hcov, ?_, fun g hg1 hgs hW => ?_⟩
  · obtain ⟨g, hg1, hgr, hW⟩ := hGA.2.1
    exact ⟨g, hg1, mul_left_cancel₀ hθ hgr, hW⟩
  · have hgr : (b : ZMod p) * constantCoeff (g 1) = (b : ZMod p) * constantCoeff (g 0) := by rw [hgs]
    have hseq := (hGA.2.2 g hg1 hgr hW).1
    refine ⟨hseq, _, hlt, fun K hK => dom p (by omega) _ hseq (g2A p) b hbA hAb hW K hK⟩

end GeoSeq
