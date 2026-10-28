/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V6A

@[expose] public section

/-!
# GeoSeq stage V6: the staggered designs for `s = 4, 5` (`tab:BSdata`, the thresholds after `thm:A`)

* **`A4_design`**, **`A5_design`**: `δ`, `L` are the least values of `lem:R`, the constants `g_c`, `u = (999/1000) ε /
  max_t |n_{j_t←⋆}|`, and the stored rows are the orders of strictly decreasing steps (`def:BS` (S3)).
* **`A4_threshold`**: `𝒫(p₀)` at the exact bisection endpoint `p₀ = 14 314 526 192 182 751`,
  `32044 < M⋆^+(p₀) < 32044.14`, and `𝒫` fails at `1.43·10^16`. **`A5_threshold`**: `𝒫(p₀)` at
  `p₀ = 1 978 313 734 082 584 379 393`, `2 722 234 324 < M⋆^+(p₀) < 2.72224·10^9`. One exact rational evaluation
  each (kernel `decide`).
* **`A4`**: every prime `p ≥ 1.44·10^16`: `c(P_{4K}) ≥ 1 - 32044/p` for every `K`; **`A5`**: every prime
  `p ≥ 1.98·10^21`: `c(P_{5K}) ≥ 1 - 2.73·10^9/p`; quasi-uniform; every selection rule.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Inst

variable {s : ℕ}

instance instDecSdOK (D : StagDesign s) : Decidable (sdOK D) := by unfold sdOK; infer_instance
instance instDecSdDeltaOK (D : StagDesign s) (δ : ℕ) : Decidable (sdDeltaOK D δ) := by
  unfold sdDeltaOK; infer_instance
instance instDecSdLOK (D : StagDesign s) (δ L : ℕ) : Decidable (sdLOK D δ L) := by unfold sdLOK; infer_instance

end Inst

/-! ## A structurally recursive `v₂` (kernel-friendly evaluation of `sdDeltaOK`) -/

/-- `v₂(n)` with fuel `k` (structural recursion; `padicValNat` itself is defined by well-founded recursion). -/
def v2f : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if n ≠ 0 ∧ n % 2 = 0 then v2f k (n / 2) + 1 else 0

lemma v2f_eq : ∀ k n : ℕ, n ≤ k → padicValNat 2 n = v2f k n
  | 0, n, h => by
    obtain rfl : n = 0 := by omega
    simp [v2f]
  | k + 1, n, h => by
    simp only [v2f]
    by_cases hn : n = 0
    · subst hn; simp
    by_cases h2 : n % 2 = 0
    · rw [if_pos ⟨hn, h2⟩]
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      have hm : m ≠ 0 := by omega
      rw [padicValNat.mul (by norm_num) hm, padicValNat.self (by norm_num), Nat.mul_div_cancel_left _ (by norm_num),
        ← v2f_eq k m (by omega)]
      ring
    · rw [if_neg (by tauto)]
      exact padicValNat.eq_zero_of_not_dvd (by omega)

lemma padicValInt_two_eq (z : ℤ) : padicValInt 2 z = v2f z.natAbs z.natAbs := v2f_eq _ _ le_rfl

/-- `sdDeltaOK` with `v₂` computed by `v2f`. -/
def sdDeltaOKc {s : ℕ} (D : StagDesign s) (δ : ℕ) : Prop :=
  (∀ j : Fin s, j ≠ D.cs →
    v2f (sdDelta D j D.cs * sdDelta D D.cs j).natAbs (sdDelta D j D.cs * sdDelta D D.cs j).natAbs ≤ 1 + 2 * δ) ∧
  ∀ j j' : Fin s, j ≠ D.cs → j' ≠ D.cs → j ≠ j' →
    v2f (sdDelta D D.cs j).natAbs (sdDelta D D.cs j).natAbs + v2f (sdDelta D j j').natAbs (sdDelta D j j').natAbs ≤
      δ + v2f (sdDelta D D.cs j').natAbs (sdDelta D D.cs j').natAbs

instance instDecSdDeltaOKc {s : ℕ} (D : StagDesign s) (δ : ℕ) : Decidable (sdDeltaOKc D δ) := by
  unfold sdDeltaOKc; infer_instance

lemma sdDeltaOK_iff {s : ℕ} (D : StagDesign s) (δ : ℕ) : sdDeltaOK D δ ↔ sdDeltaOKc D δ := by
  simp only [sdDeltaOK, sdDeltaOKc, padicValInt_two_eq]

lemma dvd_of_den_div (L q : ℕ) (hq : 0 < q) (h : ((L : ℚ) / q).den = 1) : q ∣ L := by
  have hx : (((L : ℚ) / q).num : ℚ) = (L : ℚ) / q := Rat.coe_int_num_of_den_eq_one h
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have : (L : ℚ) = ((L : ℚ) / q).num * q := by rw [hx]; field_simp
  have hz : (L : ℤ) = ((L : ℚ) / q).num * q := by exact_mod_cast this
  exact Int.natCast_dvd_natCast.mp ⟨_, by rw [hz]; ring⟩

/-! ## `s = 4` -/

/-- **The `s = 4` design** (`tab:BSdata`): `δ = 2` and `L = 3 581 577` are the least values of `lem:R`,
`g = (1, 612, -46818, 1591812)`, `u = (999/1000)(7/250)/|n_{3←0}|` with `n_{3←0}` the largest step of column `c⋆`,
and the stored rows (`taRows 4`) are the orders of strictly decreasing steps. -/
theorem A4_design :
    sdOK a4Design ∧ IsLeast {δ | sdDeltaOK a4Design δ} 2 ∧ IsLeast {L | sdLOK a4Design 2 L} 3581577 ∧
    (sdG a4Design 2 0 = 1 ∧ sdG a4Design 2 1 = 612 ∧ sdG a4Design 2 2 = -46818 ∧ sdG a4Design 2 3 = 1591812) ∧
    (∀ j : Fin 4, |sdN a4Design 2 3581577 j 0| ≤ |sdN a4Design 2 3581577 3 0|) ∧
    a4u = 999 / 1000 * (7 / 250) / |sdN a4Design 2 3581577 3 0| ∧
    (∀ c' : Fin 4, ∀ t < 2, stCoef a4Data c' (taRows 4 c' (t + 1)) < stCoef a4Data c' (taRows 4 c' t)) := by
  have hn : sdN a4Design 2 3581577 3 0 = 1266932721672 := by decide +kernel
  refine ⟨by decide +kernel, ⟨(sdDeltaOK_iff _ _).2 (by decide +kernel), fun δ hδ => ?_⟩, ⟨by decide +kernel, fun L hL => ?_⟩,
    by decide +kernel, by decide +kernel, by rw [hn]; unfold a4u; norm_num, by decide +kernel⟩
  · by_contra h
    push Not at h
    have hδ' := (sdDeltaOK_iff _ _).1 hδ
    interval_cases δ <;> revert hδ' <;> decide +kernel
  · obtain ⟨hodd, hQ, -⟩ : sdLOK a4Design 2 L := hL
    have h1 := hQ 3 (by decide +kernel)
    have hq : a4Design.Q 3 = ((3581577 : ℕ) : ℚ) := by
      simp only [a4Design, taDesign]; norm_num
    rw [hq] at h1
    have hd := dvd_of_den_div L 3581577 (by norm_num) h1
    have hL0 : 0 < L := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hodd; exact absurd hodd (by norm_num))
    exact Nat.le_of_dvd hL0 hd

theorem a4Data_valid : a4Data.Valid := by decide +kernel

/-- **The `s = 4` threshold** (`tab:BSdata`, `app:LFdata`): `𝒫(p₀)` at `p₀ = 14 314 526 192 182 751`,
`32044 < M⋆^+(p₀) < 32044.14`, and `𝒫(1.43·10^16)` fails. -/
theorem A4_threshold : StP a4Data (14314526192182751 : ℚ) ∧
    32044 < stMstP a4Data (14314526192182751 : ℚ) ∧ stMstP a4Data (14314526192182751 : ℚ) < 3204414 / 100 ∧
    ¬ StP a4Data (14300000000000000 : ℚ) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## `s = 5` -/

/-- **The `s = 5` design** (`tab:BSdata`): `c⋆ = 4`, order `(0,1,2,3)`, `Q_r = 99^r`; `δ = 5` and `L = 96 059 601`
are the least values of `lem:R`, `g = (-66, 34848, -7762392, 1024635744, 1)`, `u = (999/1000)(23/1000)/|n_{3←4}|`
with `n_{3←4}` the largest step of column `c⋆`, and the stored rows are the orders of strictly decreasing steps. -/
theorem A5_design :
    sdOK a5Design ∧ IsLeast {δ | sdDeltaOK a5Design δ} 5 ∧ IsLeast {L | sdLOK a5Design 5 L} 96059601 ∧
    (sdG a5Design 5 0 = -66 ∧ sdG a5Design 5 1 = 34848 ∧ sdG a5Design 5 2 = -7762392 ∧
      sdG a5Design 5 3 = 1024635744 ∧ sdG a5Design 5 4 = 1) ∧
    (∀ j : Fin 5, |sdN a5Design 5 96059601 j 4| ≤ |sdN a5Design 5 96059601 3 4|) ∧
    a5u = 999 / 1000 * (23 / 1000) / |sdN a5Design 5 96059601 3 4| ∧
    (∀ c' : Fin 5, ∀ t < 3, stCoef a5Data c' (a5Rows c' (t + 1)) < stCoef a5Data c' (a5Rows c' t)) := by
  have hn : sdN a5Design 5 96059601 3 4 = 131234800985304192 := by decide +kernel
  refine ⟨by decide +kernel, ⟨(sdDeltaOK_iff _ _).2 (by decide +kernel), fun δ hδ => ?_⟩, ⟨by decide +kernel, fun L hL => ?_⟩,
    by decide +kernel, by decide +kernel, by rw [hn]; unfold a5u; norm_num, by decide +kernel⟩
  · by_contra h
    push Not at h
    have hδ' := (sdDeltaOK_iff _ _).1 hδ
    interval_cases δ <;> revert hδ' <;> decide +kernel
  · obtain ⟨hodd, hQ, -⟩ : sdLOK a5Design 5 L := hL
    have h1 := hQ 3 (by decide +kernel)
    have hq : a5Design.Q 3 = ((96059601 : ℕ) : ℚ) := by
      simp only [a5Design]; norm_num
    rw [hq] at h1
    have hd := dvd_of_den_div L 96059601 (by norm_num) h1
    have hL0 : 0 < L := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hodd; exact absurd hodd (by norm_num))
    exact Nat.le_of_dvd hL0 hd

theorem a5Data_valid : a5Data.Valid := by decide +kernel

/-- **The `s = 5` threshold** (`tab:BSdata`, `app:LFdata`): `𝒫(p₀)` at `p₀ = 1 978 313 734 082 584 379 393`, with
`2 722 234 324 < M⋆^+(p₀) < 2.72224·10^9`. -/
theorem A5_threshold : StP a5Data (1978313734082584379393 : ℚ) ∧
    2722234324 < stMstP a5Data (1978313734082584379393 : ℚ) ∧
    stMstP a5Data (1978313734082584379393 : ℚ) < 2722240000 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩



/-! ## The instances -/

section Inst45

variable {p : ℕ} [Fact p.Prime]

/-- **`thm:A`, the 4-dimensional instance** (`tab:BSdata`, text after `thm:A`): for every prime `p ≥ 1.44·10^16`, the
local roots of the Faure frame `(0,…,3)` with scale `θ = 2^δ L T` exist; for every choice of them, with the
constants `g_c` of `lem:R`, the window fraction `ε = 7/250` and the `u` of `tab:BSdata` (`def:BS`), selection rules
exist, and every selection rule — and every multiplier family with these constants and all responses in the windows —
gives a digital `(0,4)`-sequence over `𝔽_p` with `c(P_{4K}) ≥ 1 - 32044/p` for every `K ≥ 1`, quasi-uniform
(`h(P_{[N]}) ≤ (√4 p/(1 - 32044/p)) · 2δ(P_{[N]})` for every `N ≥ 2`). -/
theorem A4 (hp : 14400000000000000 ≤ p) :
    (∃ zθ : Fin 4 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 4 a4Design.fr) = C (sdTheta p 2 3581577 (stT a4u p)) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA a4Design.fr c : ℤ) : ZMod p)) ∧
    ∀ zθ : Fin 4 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 4 a4Design.fr) = C (sdTheta p 2 3581577 (stT a4u p)) * X) →
      (∀ c, constantCoeff (zθ c) = ((frameA a4Design.fr c : ℤ) : ZMod p)) →
      (∃ rule : Fin 4 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ (stWin a4Data p) rule) ∧
      (∀ rule : Fin 4 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ (stWin a4Data p) rule →
        IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ rule) zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 4 K
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ rule) zθ))
          (1 - 32044 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N
            (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ rule) zθ))) ≤
            Real.sqrt 4 * p / (1 - 32044 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ rule) zθ))))) ∧
      ∀ g : Fin 4 → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam a4Design p 2 c) →
        RespInS (ssGen g zθ) (stWin a4Data p) →
        IsSeq0 (zcode p) (ssGen g zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 4 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 32044 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
            Real.sqrt 4 * p / (1 - 32044 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  obtain ⟨hok, -, ⟨hL, -⟩, -⟩ := A4_design
  obtain ⟨hP0q, -, hMq, -⟩ := A4_threshold
  have hP0 : StP a4Data ((14314526192182751 : ℕ) : ℚ) := by
    rw [show ((14314526192182751 : ℕ) : ℚ) = 14314526192182751 by norm_num]; exact hP0q
  have hpR : (14400000000000000 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : 14314526192182751 ≤ p := by omega
  have hbig := P0_big a4Design (by norm_num) hok 2 3581577 hL (taRows 4) (7 / 250) (7 / 250) (7 / 250) a4u a4Data_valid (by unfold a4u; norm_num) 14314526192182751 hP0
    (by decide +kernel) (by decide +kernel) (by norm_num) p hpp
  refine ⟨hbig.1, fun zθ hroot hplace => ?_⟩
  obtain ⟨hMst, hex, hall, hfam⟩ := hbig.2 zθ hroot hplace
  have hMst' : (stMv a4Data p a4Data.cs : ℝ) ≤ stMstP a4Data ((14314526192182751 : ℕ) : ℝ) := hMst
  have hM0 : stMstP a4Data ((14314526192182751 : ℕ) : ℝ) < 32045 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hMq
    rw [stMstP_cast] at h
    rw [show ((14314526192182751 : ℕ) : ℝ) = (((14314526192182751 : ℚ)) : ℝ) by push_cast; ring]
    refine h.trans_le ?_
    norm_num
  have hMC : (stMv a4Data p a4Data.cs : ℝ) ≤ 32044 := by
    have h1 : (stMv a4Data p a4Data.cs : ℝ) < 32044 + 1 := by
      have := hMst'.trans_lt hM0; norm_num at this ⊢; linarith
    have h2 : stMv a4Data p a4Data.cs < 32044 + 1 := by exact_mod_cast h1
    have h3 : stMv a4Data p a4Data.cs ≤ 32044 := by omega
    exact_mod_cast h3
  have hpR0 : (0 : ℝ) < p := by linarith
  have hmono : 1 - 32044 / (p : ℝ) ≤ 1 - (stMv a4Data p a4Data.cs : ℝ) / p := by
    have := div_le_div_of_nonneg_right hMC hpR0.le
    linarith
  have hpos : 0 < 1 - 32044 / (p : ℝ) := by
    have : 32044 / (p : ℝ) < 1 := by rw [div_lt_one hpR0]; linarith
    linarith
  refine ⟨hex, fun rule hrule => ?_, fun g hg hlg hW => ?_⟩
  · obtain ⟨hseq, hsep, -, -⟩ := hall rule hrule
    have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p 4 K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 3581577 (stT a4u p)) (sdLam a4Design p 2) zθ rule) zθ))
        (1 - 32044 / p) := fun K hK => sepAtLevel_le (hsep K hK) hmono
    exact ⟨hseq, hsep', fun N hN => by
      have := prefix_mesh (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep' N hN
      simpa using this⟩
  · obtain ⟨hseq, hsep, -, -⟩ := hfam g hg hlg hW
    have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p 4 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 32044 / p) :=
      fun K hK => sepAtLevel_le (hsep K hK) hmono
    exact ⟨hseq, hsep', fun N hN => by
      have := prefix_mesh (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep' N hN
      simpa using this⟩

/-- **`thm:A`, the 5-dimensional instance** (`tab:BSdata`, text after `thm:A`): for every prime `p ≥ 1.98·10^21`, the
local roots of the Faure frame `(0,…,4)` with scale `θ = 2^δ L T` exist; for every choice of them, with the
constants `g_c` of `lem:R`, the window fraction `ε = 23/1000` and the `u` of `tab:BSdata` (`def:BS`), selection rules
exist, and every selection rule — and every multiplier family with these constants and all responses in the windows —
gives a digital `(0,5)`-sequence over `𝔽_p` with `c(P_{5K}) ≥ 1 - 2.73·10^9/p` for every `K ≥ 1`, quasi-uniform
(`h(P_{[N]}) ≤ (√5 p/(1 - 2.73·10^9/p)) · 2δ(P_{[N]})` for every `N ≥ 2`). -/
theorem A5 (hp : 1980000000000000000000 ≤ p) :
    (∃ zθ : Fin 5 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 5 a5Design.fr) = C (sdTheta p 5 96059601 (stT a5u p)) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA a5Design.fr c : ℤ) : ZMod p)) ∧
    ∀ zθ : Fin 5 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 5 a5Design.fr) = C (sdTheta p 5 96059601 (stT a5u p)) * X) →
      (∀ c, constantCoeff (zθ c) = ((frameA a5Design.fr c : ℤ) : ZMod p)) →
      (∃ rule : Fin 5 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ (stWin a5Data p) rule) ∧
      (∀ rule : Fin 5 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ (stWin a5Data p) rule →
        IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ rule) zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 5 K
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ rule) zθ))
          (1 - 2730000000 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N
            (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ rule) zθ))) ≤
            Real.sqrt 5 * p / (1 - 2730000000 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ rule) zθ))))) ∧
      ∀ g : Fin 5 → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam a5Design p 5 c) →
        RespInS (ssGen g zθ) (stWin a5Data p) →
        IsSeq0 (zcode p) (ssGen g zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 5 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 2730000000 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
            Real.sqrt 5 * p / (1 - 2730000000 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  obtain ⟨hok, -, ⟨hL, -⟩, -⟩ := A5_design
  obtain ⟨hP0q, -, hMq⟩ := A5_threshold
  have hP0 : StP a5Data ((1978313734082584379393 : ℕ) : ℚ) := by
    rw [show ((1978313734082584379393 : ℕ) : ℚ) = 1978313734082584379393 by norm_num]; exact hP0q
  have hpR : (1980000000000000000000 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : 1978313734082584379393 ≤ p := by omega
  have hbig := P0_big a5Design (by norm_num) hok 5 96059601 hL a5Rows (23 / 1000) (23 / 1000) (23 / 1000) a5u a5Data_valid (by unfold a5u; norm_num) 1978313734082584379393 hP0
    (by decide +kernel) (by decide +kernel) (by norm_num) p hpp
  refine ⟨hbig.1, fun zθ hroot hplace => ?_⟩
  obtain ⟨hMst, hex, hall, hfam⟩ := hbig.2 zθ hroot hplace
  have hMst' : (stMv a5Data p a5Data.cs : ℝ) ≤ stMstP a5Data ((1978313734082584379393 : ℕ) : ℝ) := hMst
  have hM0 : stMstP a5Data ((1978313734082584379393 : ℕ) : ℝ) < 2730000001 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hMq
    rw [stMstP_cast] at h
    rw [show ((1978313734082584379393 : ℕ) : ℝ) = (((1978313734082584379393 : ℚ)) : ℝ) by push_cast; ring]
    refine h.trans_le ?_
    norm_num
  have hMC : (stMv a5Data p a5Data.cs : ℝ) ≤ 2730000000 := by
    have h1 : (stMv a5Data p a5Data.cs : ℝ) < 2730000000 + 1 := by
      have := hMst'.trans_lt hM0; norm_num at this ⊢; linarith
    have h2 : stMv a5Data p a5Data.cs < 2730000000 + 1 := by exact_mod_cast h1
    have h3 : stMv a5Data p a5Data.cs ≤ 2730000000 := by omega
    exact_mod_cast h3
  have hpR0 : (0 : ℝ) < p := by linarith
  have hmono : 1 - 2730000000 / (p : ℝ) ≤ 1 - (stMv a5Data p a5Data.cs : ℝ) / p := by
    have := div_le_div_of_nonneg_right hMC hpR0.le
    linarith
  have hpos : 0 < 1 - 2730000000 / (p : ℝ) := by
    have : 2730000000 / (p : ℝ) < 1 := by rw [div_lt_one hpR0]; linarith
    linarith
  refine ⟨hex, fun rule hrule => ?_, fun g hg hlg hW => ?_⟩
  · obtain ⟨hseq, hsep, -, -⟩ := hall rule hrule
    have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p 5 K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 5 96059601 (stT a5u p)) (sdLam a5Design p 5) zθ rule) zθ))
        (1 - 2730000000 / p) := fun K hK => sepAtLevel_le (hsep K hK) hmono
    exact ⟨hseq, hsep', fun N hN => by
      have := prefix_mesh (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep' N hN
      simpa using this⟩
  · obtain ⟨hseq, hsep, -, -⟩ := hfam g hg hlg hW
    have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p 5 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 2730000000 / p) :=
      fun K hK => sepAtLevel_le (hsep K hK) hmono
    exact ⟨hseq, hsep', fun N hN => by
      have := prefix_mesh (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep' N hN
      simpa using this⟩

end Inst45

end GeoSeq
