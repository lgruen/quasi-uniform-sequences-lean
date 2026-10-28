/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.G2

@[expose] public section

/-!
# GeoSeq stage S7: the brick hybrid (`lem:HBcov`, `thm:HB`, `cor:HB17`)

* `cover_odd`: with `ν = 2b + 1`, every integer `m ∈ [ν lo + 2b, ν hi - 2b]` is `ν i + 2ξ` with
  `i ∈ [lo, hi]`, `|ξ| ≤ b` (the even numbers `2ξ` form a complete residue system modulo the odd `ν`).
* **`HBcov`** (`lem:HBcov`, with conditions (i) and `κ_{0←1} κ_{1←0} = θ²`).
* **`HB`** (`thm:HB`): every choice of `thm:GA` gives a `(0,2)`-sequence with `c(P_{2K}) ≥ min(1, LB^HB)`.
* `hbOK_spec`, `hbCheck_spec`: the reflected integer checker and its correctness; `hb_range`: the
  finite range `3677 < p < 10^4` by kernel evaluation (`decide`); `hb_large`: `p ≥ 10^4` by hand.
* **`HB17`** (`cor:HB17`).
-/

namespace GeoSeq

open Finset PowerSeries

/-- With `ν = 2b + 1`, every integer `m` with `ν lo + 2b ≤ m ≤ ν hi - 2b` is `ν i + 2ξ` with
`lo ≤ i ≤ hi` and `-b ≤ ξ ≤ b`. -/
theorem cover_odd (b lo hi m : ℤ) (hb : 0 ≤ b) (h1 : (2 * b + 1) * lo + 2 * b ≤ m)
    (h2 : m ≤ (2 * b + 1) * hi - 2 * b) :
    ∃ i ξ : ℤ, lo ≤ i ∧ i ≤ hi ∧ -b ≤ ξ ∧ ξ ≤ b ∧ m = (2 * b + 1) * i + 2 * ξ := by
  set ν := 2 * b + 1 with hν
  have hν0 : 0 < ν := by omega
  set r := (m * (b + 1)) % ν with hr
  set q := (m * (b + 1)) / ν with hq
  have hrq : m * (b + 1) = ν * q + r := by
    rw [hq, hr]; linarith [Int.mul_ediv_add_emod (m * (b + 1)) ν]
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hν0.ne'
  have hr1 : r < ν := Int.emod_lt_of_pos _ hν0
  -- `m - 2r = ν (2q - m)`
  have hm : m - 2 * r = ν * (2 * q - m) := by rw [hν] at hrq ⊢; linear_combination 2 * hrq
  obtain ⟨i, ξ, hξ1, hξ2, hmi⟩ : ∃ i ξ : ℤ, -b ≤ ξ ∧ ξ ≤ b ∧ m = ν * i + 2 * ξ := by
    rcases le_or_gt r b with h | h
    · exact ⟨2 * q - m, r, by omega, h, by linarith⟩
    · exact ⟨2 * q - m + 2, r - ν, by omega, by omega, by linear_combination hm⟩
  refine ⟨i, ξ, ?_, ?_, hξ1, hξ2, hmi⟩
  · by_contra hc
    have : ν * i ≤ ν * (lo - 1) := mul_le_mul_of_nonneg_left (by omega) hν0.le
    nlinarith
  · by_contra hc
    have : ν * (hi + 1) ≤ ν * i := mul_le_mul_of_nonneg_left (by omega) hν0.le
    nlinarith

lemma hb_odd (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : p % 2 = 1 := by
  by_contra hc
  have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

lemma eq_neg_of' {R : Type*} [Ring R] {x y : R} (h : y = -x) : x = -y := by rw [h, neg_neg]

lemma k10_alg {F : Type*} [Field F] (ν h b : F) (h2 : (2 : F) ≠ 0) (hh : 2 * h = 1)
    (hν : ν = 2 * b + 1) : -ν * (2 : F)⁻¹ = -(h + b) := by
  rw [hν]; field_simp; linear_combination hh

lemma col0_alg {F : Type*} [Field F] (ν h i ξ N β : F) (h2 : (2 : F) ≠ 0) (hh : 2 * h = 1)
    (hN : N = ν * i + 2 * ξ + 1) (hNβ : N = -(2 * β)) :
    -ν * (2 : F)⁻¹ * ((i + 1) - 1) - (h + ξ) = β := by
  field_simp
  linear_combination hN - hNβ - hh

lemma two_ne_zero' (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : (2 : ZMod p) ≠ 0 :=
  two_ne_zero_zmod p (by omega)

/-- `ν (M_A - 3) ≥ p - 3`. -/
lemma hbMA_ge (p b : ℕ) : p - 3 ≤ hbNu b * (hbMA p b - 3) := by
  have hν : 0 < hbNu b := by unfold hbNu; omega
  have h1 := Nat.div_add_mod (p - 3 + hbNu b - 1) (hbNu b)
  have h2 := Nat.mod_lt (p - 3 + hbNu b - 1) hν
  unfold hbMA
  rw [Nat.add_sub_cancel]
  omega

/-- `k (M_B + 1) ≥ p - 1` and `M_B ≥ 1` when `k + 1 < p`. -/
lemma hbMB_ge (p b e : ℕ) (hk0 : 0 < hbK b e) (hk : hbK b e + 1 < p) :
    p - 1 ≤ hbK b e * (hbMB p b e + 1) ∧ 1 ≤ hbMB p b e := by
  have h1 := Nat.div_add_mod (p - 1 + hbK b e - 1) (hbK b e)
  have h2 := Nat.mod_lt (p - 1 + hbK b e - 1) hk0
  have h3 : 2 ≤ (p - 1 + hbK b e - 1) / hbK b e := by
    rw [Nat.le_div_iff_mul_le hk0]; omega
  unfold hbMB
  constructor
  · rw [Nat.sub_add_cancel (by omega)]; omega
  · omega

/-- **`lem:HBcov`** (with condition (i) of `thm:GA` and the square condition): for the brick hybrid
data (`b, e ≥ 1`, `ν = 2b + 1 < p`, `3k < p`), `κ_{0←1} κ_{1←0} = θ²`, `-κ_{1←0} = ν/2 ∈ W_x^{(0)}`,
`-κ_{0←1} = k ∈ W_x^{(1)}`, and both columns satisfy condition (ii). -/
theorem HBcov (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hν : hbNu b < p) (hk : 3 * hbK b e < p) :
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

/-! ## `thm:HB` -/

lemma sq_terms_le (P : ℝ) (hP : 0 < P) (u v U V : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ U) (hv0 : 0 ≤ v)
    (hv : v ≤ V) : (u / P) ^ 2 + (v / P) ^ 2 ≤ (U / P) ^ 2 + (V / P) ^ 2 := by
  have h1 : (u / P) ^ 2 ≤ (U / P) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hu0 hP.le) (div_le_div_of_nonneg_right hu hP.le) 2
  have h2 : (v / P) ^ 2 ≤ (V / P) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hv0 hP.le) (div_le_div_of_nonneg_right hv hP.le) 2
  linarith

lemma gnR (p : ℕ) (e : ℤ) (σ : ZMod p) [NeZero p] (B : ℤ) (h : B ≤ (gapNum1 p e σ : ℤ)) :
    (B : ℝ) ≤ (gapNum1 p e σ : ℝ) := by exact_mod_cast h

/-- **`thm:HB`** (brick hybrid): with `b, e ≥ 1`, `ν = 2b+1 < p`, `3k < p`, `2k + M_A < p` and
`η > 0` (`2b + 2M_B + 1 < p`), the scramble of `thm:GA` with the windows of the brick hybrid exists, and
every choice gives a `(0,2)`-sequence with `c(P_{2K}) ≥ min(1, LB^HB)` for every `K ≥ 1`. -/
theorem HB (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hν : hbNu b < p) (hk : 3 * hbK b e < p) (hka : 2 * hbK b e + hbMA p b < p)
    (hη : 2 * b + 2 * hbMB p b e + 1 < p) :
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e)) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (hbTheta p b e))) ∧
        ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p b e))))
          (min 1 (Real.sqrt (hbLB2 p b e)))) := by
  obtain ⟨hsq, hi0, hi1, hc0, hc1⟩ := HBcov p hp b e hb he hν hk
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

/-! ## `cor:HB17`: the integer conditions -/

/-- Correctness of the reflected checker `hbOK`. -/
theorem hbOK_spec (p : ℕ) : hbOK p = true ↔ HBConds p := by
  unfold hbOK HBConds
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Correctness of `smallDiv`: a small divisor `2 ≤ d < 20`. -/
theorem smallDiv_spec (n : ℕ) (h : smallDiv n = true) : ∃ d, 2 ≤ d ∧ d < 20 ∧ d ∣ n := by
  unfold smallDiv at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi, hd⟩ := h
  rw [List.mem_range] at hi
  refine ⟨i + 2, by omega, by omega, Nat.dvd_of_mod_eq_zero ?_⟩
  simpa using hd

/-- Correctness of the range checker `hbCheck`. -/
theorem hbCheck_spec (cnt : ℕ) : ∀ lo, hbCheck lo cnt = true →
    ∀ n, lo ≤ n → n < lo + cnt → hbOK n = true ∨ smallDiv n = true := by
  induction cnt with
  | zero => intro lo _ n h1 h2; omega
  | succ c ih =>
    intro lo h n h1 h2
    simp only [hbCheck, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.1
    · exact ih (lo + 1) h.2 n (by omega) (by omega)

set_option maxRecDepth 100000 in
/-- The finite range `3678 ≤ n < 10^4`, evaluated by the kernel (`decide`, no `native_decide`). -/
theorem hb_check_range : hbCheck 3678 6322 = true := by decide +kernel

/-- `cor:HB17`, finite range: every prime `3677 < p < 10^4` satisfies the integer conditions. -/
theorem hb_range (p : ℕ) (hp : p.Prime) (h1 : 3677 < p) (h2 : p < 10000) : HBConds p := by
  rw [← hbOK_spec]
  rcases hbCheck_spec 6322 3678 hb_check_range p (by omega) (by omega) with h | h
  · exact h
  · obtain ⟨d, hd2, hd20, hdvd⟩ := smallDiv_spec p h
    rcases hp.eq_one_or_self_of_dvd d hdvd with h' | h' <;> omega

/-- `cor:HB17`, the hand range: every `p ≥ 10^4` satisfies the integer conditions (written proof:
`p = 68b + r`, `0 ≤ r < 68`, `b ≥ 147`; `M_A ≤ 38`, `M_B ≤ 17`; two quadratic inequalities in `b, r`). -/
theorem hb_large (p : ℕ) (hp : 10000 ≤ p) : HBConds p := by
  unfold HBConds
  set b := p / 68 with hbdef
  have hb1 := Nat.div_add_mod p 68
  have hb2 := Nat.mod_lt p (show 0 < 68 by norm_num)
  rw [← hbdef] at hb1
  set r := p % 68
  have hb147 : 147 ≤ b := by omega
  have hν : hbNu b = 2 * b + 1 := rfl
  have hk : hbK b 1 = 4 * b + 2 := by unfold hbK hbNu; ring
  -- `M_A ≤ 38`
  have hma : hbMA p b ≤ 38 := by
    unfold hbMA
    rw [hν]
    have : (p - 3 + (2 * b + 1) - 1) / (2 * b + 1) < 36 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  -- `M_B ≤ 17`
  have hmb : hbMB p b 1 ≤ 17 := by
    unfold hbMB
    rw [hk]
    have : (p - 1 + (4 * b + 2) - 1) / (4 * b + 2) < 19 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  rw [hν, hk]
  refine ⟨by omega, by omega, by omega, by omega, hmb, by omega, ?_, ?_⟩
  · 
    set A := hbMA p b
    zify [show 4 * b + 2 ≤ p by omega, show A ≤ p - (4 * b + 2) by omega, show 3 ≤ p by omega,
      show 2 * b ≤ p - 3 by omega, show 17 ≤ p by omega]
    have hA : (A : ℤ) ≤ 38 := by exact_mod_cast hma
    have hA0 : (0 : ℤ) ≤ A := by positivity
    have hpz : (p : ℤ) = 68 * b + r := by omega
    have hr : (r : ℤ) < 68 := by omega
    have hbz : (147 : ℤ) ≤ b := by exact_mod_cast hb147
    have h1 : (p : ℤ) - (4 * b + 2) - 38 ≤ (p : ℤ) - (4 * b + 2) - A := by linarith
    have h0 : (0 : ℤ) ≤ (p : ℤ) - (4 * b + 2) - 38 := by omega
    have hsq := mul_le_mul h1 h1 h0 (by linarith)
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have key : 0 ≤ (66 * (b : ℤ) + r - 3) ^ 2 - 4 * (4 * b + 23) * (132 * b + 2 * r - 57) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ b - 147 by linarith) (show (0 : ℤ) ≤ b by linarith),
        mul_nonneg (show (0 : ℤ) ≤ b by linarith) hr0, sq_nonneg (r : ℤ)]
    rw [hpz] at hsq ⊢
    linarith
  · set A := hbMA p b
    set M := hbMB p b 1
    zify [show 2 * (4 * b + 2) ≤ p by omega, show A ≤ p - 2 * (4 * b + 2) by omega,
      show 1 ≤ p by omega, show 2 * b ≤ p - 1 by omega, show 2 * M ≤ p - 1 - 2 * b by omega,
      show 17 ≤ p by omega]
    have hA : (A : ℤ) ≤ 38 := by exact_mod_cast hma
    have hM : (M : ℤ) ≤ 17 := by exact_mod_cast hmb
    have hA0 : (0 : ℤ) ≤ A := by positivity
    have hM0 : (0 : ℤ) ≤ M := by positivity
    have hpz : (p : ℤ) = 68 * b + r := by omega
    have hr : (r : ℤ) < 68 := by omega
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hbz : (147 : ℤ) ≤ b := by exact_mod_cast hb147
    have h1 : (p : ℤ) - 2 * (4 * b + 2) - 38 ≤ (p : ℤ) - 2 * (4 * b + 2) - A := by linarith
    have h0 : (0 : ℤ) ≤ (p : ℤ) - 2 * (4 * b + 2) - 38 := by omega
    have h2 : (p : ℤ) - 1 - 2 * b - 34 ≤ (p : ℤ) - 1 - 2 * b - 2 * M := by linarith
    have h0' : (0 : ℤ) ≤ (p : ℤ) - 1 - 2 * b - 34 := by omega
    have hsq1 := mul_le_mul h1 h1 h0 (by linarith)
    have hsq2 := mul_le_mul h2 h2 h0' (by linarith)
    have key : 0 ≤ 4 * (60 * (b : ℤ) + r - 42) ^ 2 + (66 * b + r - 35) ^ 2 -
        4 * (68 * b + r - 17) ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ b - 147 by linarith) (show (0 : ℤ) ≤ b by linarith),
        mul_nonneg (show (0 : ℤ) ≤ b by linarith) hr0, sq_nonneg (r : ℤ)]
    rw [hpz] at hsq1 hsq2 ⊢
    linarith

/-! ## `cor:HB17` -/

lemma sq_frac_le (P u w : ℝ) (hP : 0 < P) (h : 4 * (P - 17) ^ 2 ≤ 4 * u ^ 2 + w ^ 2) :
    (1 - 17 / P) ^ 2 ≤ (u / P) ^ 2 + (w / (2 * P)) ^ 2 := by
  have e1 : (1 - 17 / P) ^ 2 = 4 * (P - 17) ^ 2 / (4 * P ^ 2) := by field_simp
  have e2 : (u / P) ^ 2 + (w / (2 * P)) ^ 2 = (4 * u ^ 2 + w ^ 2) / (4 * P ^ 2) := by
    field_simp; ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- **`cor:HB17`** (separation of order `1 - O(1/p)`): for every prime `p > 3677`, the brick hybrid with
`e = 1`, `b = ⌊p/68⌋` exists (`thm:GA`), and every such sequence is a `(0,2)`-sequence with
`c(P_{2K}) ≥ 1 - 17/p` for every `K ≥ 1` and `δ(P_{[N]}) ≥ (1 - 17/p) p^{-1} N^{-1/2}` for all `N ≥ 2`.
The range `p ≥ 10^4` is the written proof (`hb_large`); the `715` primes `3677 < p < 10^4` are checked by
the kernel (`hb_range`, reflected checker `hbCheck`, `decide`). -/
theorem HB17 (p : ℕ) [Fact p.Prime] (hp : 3677 < p) :
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      hbK01 p (p / 68) 1 * constantCoeff (g 1) = hbTheta p (p / 68) 1 * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (hbTheta p (p / 68) 1))) (hbWo p (p / 68) 1) (hbWx p (p / 68) 1)) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      hbK01 p (p / 68) 1 * constantCoeff (g 1) = hbTheta p (p / 68) 1 * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (hbTheta p (p / 68) 1))) (hbWo p (p / 68) 1) (hbWx p (p / 68) 1) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))) ∧
        (∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))))
          (1 - 17 / (p : ℝ))) ∧
        SepAllN 2 (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))))
          ((1 - 17 / (p : ℝ)) / p)) := by
  have hc : HBConds p := by
    rcases lt_or_ge p 10000 with h | h
    · exact hb_range p Fact.out hp h
    · exact hb_large p h
  obtain ⟨hν, hk, hka, hη, hmb, h17, hT1, hT3⟩ := hc
  set b := p / 68 with hbdef
  have hb : 1 ≤ b := by omega
  have hHB := HB p (by omega) b 1 hb le_rfl hν hk hka hη
  refine ⟨hHB.1, fun g hg1 hgr hW => ?_⟩
  obtain ⟨hseq, hsep⟩ := hHB.2 g hg1 hgr hW
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h17R : (0 : ℝ) ≤ 1 - 17 / p := by
    rw [sub_nonneg, div_le_one hP]; exact_mod_cast h17.le
  -- `1 - 17/p ≤ min(1, LB^HB)`
  have hLB : 1 - 17 / (p : ℝ) ≤ min 1 (Real.sqrt (hbLB2 p b 1)) := by
    refine le_min (by have : (0 : ℝ) ≤ 17 / p := by positivity
                      linarith) ?_
    apply Real.le_sqrt_of_sq_le
    unfold hbLB2
    set kk := hbK b 1
    set ma := hbMA p b
    set mb := hbMB p b 1
    refine le_min ?_ (le_min ?_ ?_)
    · have e : 1 - ((kk : ℝ) + ma) / p = ((p : ℝ) - kk - ma) / p := by
        rw [one_sub_div hP.ne']; ring
      rw [e]
      apply sq_frac_le _ _ _ hP
      have : ((4 * (p - 17) ^ 2 : ℕ) : ℝ) ≤ ((4 * (p - kk - ma) ^ 2 + (p - 3 - 2 * b) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hT1
      push_cast [show 17 ≤ p by omega, show kk ≤ p by omega, show ma ≤ p - kk by omega,
        show 3 ≤ p by omega, show 2 * b ≤ p - 3 by omega] at this
      linarith
    · have h1 : 1 - 17 / (p : ℝ) ≤ 1 - (mb : ℝ) / p := by
        have : (mb : ℝ) ≤ 17 := by exact_mod_cast hmb
        have : (mb : ℝ) / p ≤ 17 / p := div_le_div_of_nonneg_right this hP.le
        linarith
      exact pow_le_pow_left₀ h17R h1 2
    · have e : 1 - (2 * (kk : ℝ) + ma) / p = ((p : ℝ) - 2 * kk - ma) / p := by
        rw [one_sub_div hP.ne']; ring
      rw [e]
      apply sq_frac_le _ _ _ hP
      have : ((4 * (p - 17) ^ 2 : ℕ) : ℝ) ≤
          ((4 * (p - 2 * kk - ma) ^ 2 + (p - 1 - 2 * b - 2 * mb) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hT3
      push_cast [show 17 ≤ p by omega, show 2 * kk ≤ p by omega, show ma ≤ p - 2 * kk by omega,
        show 1 ≤ p by omega, show 2 * b ≤ p - 1 by omega, show 2 * mb ≤ p - 1 - 2 * b by omega] at this
      linarith
  have hlev : ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p b 1))))
      (1 - 17 / (p : ℝ)) := by
    intro K hK v w hv hw hvw
    exact le_trans hLB (hsep K hK v w hv hw hvw)
  exact ⟨hseq, hlev, prefix_sep p 2 (by omega) (by norm_num) _ _ h17R hlev⟩

end GeoSeq
