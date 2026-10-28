/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.HB

@[expose] public section

/-!
# GeoSeq stage V5: `thm:HB` in the V3 wording

The V3 statement of `thm:HB` assumes only `2k + M_A < p` and `η > 0` (and `b, e ≥ 1`); the earlier formal
statement `HB` (stage S7) also assumed `3k < p` and `ν < p`, `p ≥ 5`. `ν < p` and `p ≥ 5` follow from
`2k + M_A < p`; `3k < p` does not (e.g. `p = 431`, `b = 2`, `e = 4`: `k = 160`, `2k + M_A = 409 < 431 ≤ 3k = 480`),
but the proof only uses `k + 1 < p`. `HBcov_V3`, `HB_V3`: the proofs of `HBcov`, `HB` with that weaker
hypothesis (copied from `GeoSeq/HB.lean`; the earlier theorems are untouched).
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`lem:HBcov`** with `k + 1 < p` in place of `3k < p`. -/
theorem HBcov_V3 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hν : hbNu b < p) (hk : hbK b e + 1 < p) :
    hbK01 p b e * hbK10 p b = hbTheta p b e ^ 2 ∧
      -hbK10 p b ∈ hbWx p b e 0 ∧ -hbK01 p b e ∈ hbWx p b e 1 ∧
      Covers (hbK10 p b) (hbWo p b e 0) (hbWx p b e 0) ∧
      Covers (hbK01 p b e) (hbWo p b e 1) (hbWx p b e 1) := by
  have h2 := two_ne_zero' p hp
  have hodd := hb_odd p hp
  set h := (p + 1) / 2 with hhdef
  have hh : 2 * h = p + 1 := by omega
  have hpz : ((p : ℤ) : ZMod p) = 0 := by simp
  have hhz : (2 : ZMod p) * (h : ZMod p) = 1 := by
    have : ((2 * h : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [hh]
    push_cast at this
    rw [this, ZMod.natCast_self, zero_add]
  have hkdef : hbK b e = 2 * hbNu b * e ^ 2 := rfl
  have hk0 : 0 < hbK b e := by
    rw [hkdef]; unfold hbNu; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `k ν/2 = (ν e)²`
    unfold hbK01 hbK10 hbTheta
    rw [hkdef]
    push_cast
    field_simp
    try ring
  · -- `ν/2 = (p+1)/2 + b`
    refine ⟨(h : ℤ) + b, by omega, le_rfl, eq_neg_of' ?_⟩
    unfold hbK10
    push_cast
    exact k10_alg _ _ _ h2 hhz (by unfold hbNu; push_cast; ring)
  · refine ⟨hbK b e, by omega, le_rfl, eq_neg_of' ?_⟩
    unfold hbK01
    push_cast; rfl
  · -- column 0
    intro β
    set ν := hbNu b with hνdef
    set ma := hbMA p b with hmadef
    have hma := hbMA_ge p b
    have hma3 : 3 ≤ ma := by rw [hmadef]; unfold hbMA; exact Nat.le_add_left _ _
    set lo : ℤ := -((hbK b e : ℤ) + ma) with hlo
    set hi : ℤ := -(hbK b e : ℤ) - 1 with hhi
    obtain ⟨N, hN1, hN2, hNβ⟩ := cover_interval p ((ν : ℤ) * lo + 2 * b + 1) (-(2 * β))
    have hν' : (ν : ℤ) = 2 * b + 1 := by rw [hνdef]; unfold hbNu; push_cast; ring
    have hmaz : (p : ℤ) - 3 ≤ (ν : ℤ) * ((ma : ℤ) - 3) := by
      have : ((p - 3 : ℕ) : ℤ) ≤ ((ν * (ma - 3) : ℕ) : ℤ) := by exact_mod_cast hma
      push_cast [show 3 ≤ p by omega, hma3] at this
      exact this
    obtain ⟨i, ξ, hi1, hi2, hξ1, hξ2, hmi⟩ := cover_odd b lo hi (N - 1) (by omega)
      (by rw [← hν']; linarith) (by
        have e1 : (ν : ℤ) * lo = -((ν : ℤ) * hbK b e) - ν * ma := by rw [hlo]; ring
        have e2 : (ν : ℤ) * hi = -((ν : ℤ) * hbK b e) - ν := by rw [hhi]; ring
        have e3 : (ν : ℤ) * ((ma : ℤ) - 3) = ν * ma - 3 * ν := by ring
        rw [← hν', e2]; rw [e1] at hN2; rw [e3] at hmaz; linarith)
    refine ⟨((i + 1 : ℤ) : ZMod p), ⟨i + 1, ?_, by omega, rfl⟩, (((h : ℤ) + ξ : ℤ) : ZMod p),
      ⟨(h : ℤ) + ξ, by push_cast; omega, by push_cast; omega, rfl⟩, ?_⟩
    · rw [hlo] at hi1
      push_cast [show 1 ≤ hbK b e + ma by omega]
      omega
    · have e2 : (N : ZMod p) = (ν : ZMod p) * (i : ZMod p) + 2 * (ξ : ZMod p) + 1 := by
        have : N = (ν : ℤ) * i + 2 * ξ + 1 := by rw [← hν'] at hmi; linarith
        rw [this]; push_cast; ring
      unfold hbK10
      rw [← hνdef]
      push_cast
      exact col0_alg _ _ _ _ _ _ h2 hhz e2 hNβ
  · -- column 1
    intro β
    obtain ⟨hmb, hmb1⟩ := hbMB_ge p b e hk0 (by omega)
    obtain ⟨S, hS1, hS2, hSβ⟩ := cover_interval p 0 β
    have hmbz : (p : ℤ) - 1 ≤ (hbK b e : ℤ) * ((hbMB p b e : ℤ) + 1) := by
      have : ((p - 1 : ℕ) : ℤ) ≤ ((hbK b e * (hbMB p b e + 1) : ℕ) : ℤ) := by exact_mod_cast hmb
      push_cast [show 1 ≤ p by omega] at this
      exact this
    obtain ⟨i, ξ, hi1, hi2, hξ1, hξ2, hSi⟩ := cover_round (hbK b e) 1 (hbMB p b e) S
      (by omega) (by omega) (by linarith) (by linarith)
    refine ⟨((1 - i : ℤ) : ZMod p), ⟨1 - i, by omega, by omega, rfl⟩, (ξ : ZMod p),
      ⟨ξ, hξ1, hξ2, rfl⟩, ?_⟩
    rw [← hSβ, hSi]
    unfold hbK01
    push_cast
    ring

/-- **`thm:HB`** (hexagonal brick wall), V3 wording: if `b, e ≥ 1`, `2k + M_A < p` and `η > 0`
(`2b + 2M_B + 1 < p`), then a normalised multiplier family with all responses in the windows exists ("a selection
rule"), and every such family ("every selection rule") gives a digital `(0,2)`-sequence over `𝔽_p` with
`c(P_{2K}) ≥ min(1, LB^HB)` for every `K ≥ 1`. -/
theorem HB_V3 (p : ℕ) [Fact p.Prime] (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hka : 2 * hbK b e + hbMA p b < p) (hη : 2 * b + 2 * hbMB p b e + 1 < p) :
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e)) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (hbTheta p b e))) ∧
        ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p b e))))
          (min 1 (Real.sqrt (hbLB2 p b e)))) := by
  have hma3 : 3 ≤ hbMA p b := by unfold hbMA; exact Nat.le_add_left _ _
  have hkν : hbNu b ≤ hbK b e := by
    have : hbK b e = 2 * hbNu b * e ^ 2 := rfl
    rw [this]; nlinarith [Nat.one_le_pow 2 e he]
  have hp : 5 ≤ p := by unfold hbNu at hkν; omega
  have hν : hbNu b < p := by omega
  have hk : hbK b e + 1 < p := by omega
  obtain ⟨hsq, hi0, hi1, hc0, hc1⟩ := HBcov_V3 p hp b e hb he hν hk
  have hkdef : hbK b e = 2 * hbNu b * e ^ 2 := rfl
  have hνe : hbNu b * e ≤ hbK b e := by
    rw [hkdef]; nlinarith [Nat.one_le_pow 2 e he]
  have hνpos : 0 < hbNu b * e := by unfold hbNu; positivity
  have hθ : hbTheta p b e ≠ 0 := by
    unfold hbTheta
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd hνpos h; omega
  have h01 : hbK01 p b e ≠ 0 := by
    unfold hbK01
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hGA := GA p hp (hbTheta p b e) (hbK01 p b e) (hbK10 p b) hθ h01 hsq (hbWo p b e)
    (hbWx p b e) hi0 hi1 hc0 hc1
  refine ⟨hGA.2.1, fun g hg1 hgr hW => ?_⟩
  obtain ⟨hseq, hsep⟩ := hGA.2.2 g hg1 hgr hW
  clear hGA hc0 hc1 hi0 hi1 hsq
  refine ⟨hseq, fun K hK => hsep _ ?_ K hK⟩
  -- the four window minima
  have hodd := hb_odd p hp
  set h := (p + 1) / 2 with hhdef
  have hh : 2 * h = p + 1 := by omega
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set kk := hbK b e
  set ma := hbMA p b
  set mb := hbMB p b e
  have hmb1 : 1 ≤ mb := (hbMB_ge p b e (by unfold hbK hbNu; positivity) (by omega)).2
  have hW0o : ∀ o ∈ hbWo p b e 0, ((p : ℤ) - kk - ma) ≤ (gapNum1 p 1 o : ℤ) := by
    rintro o ⟨z, hz0, hz1, rfl⟩
    rw [f1_int_nonpos p z (by push_cast at hz0; omega) (by omega)]
    push_cast at hz0; omega
  have hW1o : ∀ o ∈ hbWo p b e 1, ((p : ℤ) - mb) ≤ (gapNum1 p 1 o : ℤ) := by
    rintro o ⟨z, hz0, hz1, rfl⟩
    rw [f1_int_nonpos p z (by omega) hz1]
    omega
  have hW0x : ∀ x ∈ hbWx p b e 0, (p : ℝ) - 3 - 2 * b ≤ 2 * (gapNum1 p 0 x : ℝ) := by
    rintro x ⟨z, hz0, hz1, rfl⟩
    rw [f0_int p z (by omega) (by omega)]
    have : (p : ℤ) - 3 - 2 * b ≤ 2 * ((min z.toNat (p - z.toNat) - 1 : ℕ) : ℤ) := by omega
    exact_mod_cast this
  have hD0 : ∀ o ∈ hbWo p b e 0, ∀ x ∈ hbWx p b e 1,
      ((p : ℤ) - 2 * kk - ma) ≤ (gapNum1 p 1 (o + x) : ℤ) ∧
        ((p : ℤ) - 2 * kk - ma) ≤ (gapNum1 p 1 (o - x) : ℤ) := by
    rintro o ⟨z, hz0, hz1, rfl⟩ x ⟨w, hw0, hw1, rfl⟩
    push_cast at hz0
    constructor
    · rw [← Int.cast_add, f1_int_nonpos p _ (by omega) (by omega)]; omega
    · rw [← Int.cast_sub, f1_int_nonpos p _ (by omega) (by omega)]; omega
  have hD1 : ∀ o ∈ hbWo p b e 1, ∀ x ∈ hbWx p b e 0,
      (p : ℝ) - 1 - 2 * b - 2 * mb ≤ 2 * (gapNum1 p 1 (o + x) : ℝ) ∧
        (p : ℝ) - 1 - 2 * b - 2 * mb ≤ 2 * (gapNum1 p 1 (o - x) : ℝ) := by
    rintro o ⟨z, hz0, hz1, rfl⟩ x ⟨w, hw0, hw1, rfl⟩
    constructor
    · rw [← Int.cast_add]
      have := f1_int_pos p (z + w) (by omega) (by omega)
      have h2 : (p : ℤ) - 1 - 2 * b - 2 * mb ≤ 2 * (gapNum1 p 1 ((z + w : ℤ) : ZMod p) : ℤ) := by
        omega
      exact_mod_cast h2
    · have e : ((z : ZMod p) - (w : ZMod p)) = ((z - w + p : ℤ) : ZMod p) := by push_cast; simp
      rw [e]
      have := f1_int_pos p (z - w + p) (by omega) (by omega)
      have h2 : (p : ℤ) - 1 - 2 * b - 2 * mb ≤
          2 * (gapNum1 p 1 ((z - w + p : ℤ) : ZMod p) : ℤ) := by omega
      exact_mod_cast h2
  have hkR : ((p : ℝ) - kk - ma) / p = 1 - ((kk : ℝ) + ma) / p := by
    rw [one_sub_div hP.ne']; ring
  have hkR2 : ((p : ℝ) - 2 * kk - ma) / p = 1 - (2 * (kk : ℝ) + ma) / p := by
    rw [one_sub_div hP.ne']; ring
  have hmR : ((p : ℝ) - mb) / p = 1 - (mb : ℝ) / p := by rw [one_sub_div hP.ne']
  have hxR : ∀ t : ℝ, ((t / 2) / p) = t / (2 * p) := fun t => by rw [div_div]
  have hpk : (0 : ℝ) ≤ (p : ℝ) - kk - ma := by
    have : ((kk + ma : ℕ) : ℝ) ≤ p := by exact_mod_cast (show kk + ma ≤ p by omega)
    push_cast at this; linarith
  have hpk2 : (0 : ℝ) ≤ (p : ℝ) - 2 * kk - ma := by
    have : ((2 * kk + ma : ℕ) : ℝ) ≤ p := by exact_mod_cast (show 2 * kk + ma ≤ p by omega)
    push_cast at this; linarith
  have hpb : (0 : ℝ) ≤ ((p : ℝ) - 3 - 2 * b) / 2 := by
    have : ((3 + 2 * b : ℕ) : ℝ) ≤ p := by exact_mod_cast (show 3 + 2 * b ≤ p by unfold hbNu at hν; omega)
    push_cast at this; linarith
  have hpη : (0 : ℝ) ≤ ((p : ℝ) - 1 - 2 * b - 2 * mb) / 2 := by
    have : ((1 + 2 * b + 2 * mb : ℕ) : ℝ) ≤ p := by exact_mod_cast (show 1 + 2 * b + 2 * mb ≤ p by omega)
    push_cast at this; linarith
  have hpm : (0 : ℝ) ≤ (p : ℝ) - mb := by
    have : (mb : ℝ) ≤ p := by exact_mod_cast (show mb ≤ p by omega)
    linarith
  unfold hbLB2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o ho x hx
    apply Real.sqrt_le_sqrt
    refine (min_le_left _ _).trans ?_
    rw [← hkR, ← hxR]
    refine sq_terms_le p hP _ _ _ _ hpk ?_ hpb ?_
    · have h1 := gnR p 1 o _ (hW0o o ho); push_cast at h1; exact h1
    · have := hW0x x hx; linarith
  · intro o ho x hx
    apply Real.sqrt_le_sqrt
    refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
    rw [← hmR]
    have h1 := gnR p 1 o _ (hW1o o ho)
    push_cast at h1
    have := sq_terms_le p hP _ 0 _ (gapNum1 p 0 x) hpm h1 le_rfl (by positivity)
    simpa using this
  · intro o0 ho0 x1 hx1 o1 ho1 x0 hx0
    apply Real.sqrt_le_sqrt
    refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
    rw [← hkR2, ← hxR]
    refine sq_terms_le p hP _ _ _ _ hpk2 ?_ hpη ?_
    · have h1 := gnR p 1 _ _ (hD0 o0 ho0 x1 hx1).1; push_cast at h1; exact h1
    · have := (hD1 o1 ho1 x0 hx0).1; linarith
  · intro o0 ho0 x1 hx1 o1 ho1 x0 hx0
    apply Real.sqrt_le_sqrt
    refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
    rw [← hkR2, ← hxR]
    refine sq_terms_le p hP _ _ _ _ hpk2 ?_ hpη ?_
    · have h1 := gnR p 1 _ _ (hD0 o0 ho0 x1 hx1).2; push_cast at h1; exact h1
    · have := (hD1 o1 ho1 x0 hx0).2; linarith

end GeoSeq
