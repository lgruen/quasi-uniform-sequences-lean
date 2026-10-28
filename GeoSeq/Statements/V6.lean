/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V6Defs

@[expose] public section

/-!
# Statements: stage V6 (`sec:antipode`, `prop:P0`(c) and `thm:A`)

`prop:P0`(c) (the limit hierarchy gives `𝒫(p)` for all large `p`; a natural threshold `p₀` exists) and `thm:A` (separation `1 - O(1/p)` in every dimension `s ≥ 3`, general statement with the `R`-hierarchy of its proof), and the `s = 4, 5` designs of `tab:BSdata` with their exact thresholds.
PROVED (`GeoSeq/V6P0c.lean`, `V6A.lean`, `V6A45.lean`); generated verbatim from the proof files' signatures by
`scripts/gen_v6_statements.py` (definitions in `GeoSeq/V6Defs.lean`, on top of `GeoSeq/V5Defs.lean`).
Paper: V3 (development version V3 of the paper, `06-antipode.tex`, `E-designs.tex`); label → Lean map in
the formalization notes of the research repository, review the statement-review notes of the research repository.
-/

namespace GeoSeq
open Finset PowerSeries Filter Topology
open scoped Polynomial

section G0
variable {s : ℕ}

/-- **`prop:P0`(c)**: if the design satisfies the limit hierarchy (`LimHier`), `0 < ε_{⋆←C} < ½`,
`x² + y² > 1` and `1 - 2(s-2)ε_{C←C} - 2ε_{C←⋆} > 1/√2` (with the positive fractions and `u > 0` of `def:BS`), then
`𝒫(p)` holds for all large real `p`. -/
theorem P0_c (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hu : 0 < D.u) (hCS : 0 < D.eCS) (hCC : 0 < D.eCC)
    (hSC : 0 < D.eSC) (hSC2 : D.eSC < 1 / 2) (hxy : 1 < stX D ^ 2 + stY D ^ 2)
    (hz : 1 / Real.sqrt 2 < 1 - 2 * ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS) (hH : LimHier (K := ℝ) D) :
    ∀ᶠ p in atTop, StP D (p : ℝ) := by
  sorry

/-- **`prop:P0`, last sentence** ("under the hypotheses of (c) such a `p₀` exists"): above every bound `N` there is
a natural number `p₀` with `𝒫(p₀)`, as an exact rational statement (decidable). -/
theorem P0_c_nat (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hu : 0 < D.u) (hCS : 0 < D.eCS)
    (hCC : 0 < D.eCC) (hSC : 0 < D.eSC) (hSC2 : D.eSC < 1 / 2) (hxy : 1 < stX D ^ 2 + stY D ^ 2)
    (hz : 1 / Real.sqrt 2 < 1 - 2 * ((s - 2 : ℕ) : ℝ) * D.eCC - 2 * D.eCS) (hH : LimHier (K := ℝ) D) (N : ℕ) :
    ∃ p0 : ℕ, N ≤ p0 ∧ 0 < p0 ∧ StP D (p0 : ℚ) := by
  sorry

end G0

section G1
variable {s : ℕ} [NeZero s]

/-- **The steps of the design** (proof of `thm:A`): the step of row `c` in column `c'`, divided by `T`, is
`L R^{c-c'} w(c,c')`, i.e. `stCoef · R^{c'} = L R^c w(c,c')`. -/
theorem stCoef_ta (R : ℕ) (hR : R % 2 = 1) (δ L : ℕ) (hL : sdLOK (taDesign s R) δ L) (rows : Fin s → ℕ → Fin s)
    (e1 e2 e3 u : ℚ) {c c' : Fin s} (h : c ≠ c') :
    (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c : ℚ) * (R : ℚ) ^ (c' : ℕ) =
      L * (R : ℚ) ^ (c : ℕ) * taW s δ c c' := by
  sorry

/-- **Consecutive steps** (proof of `thm:A`): for rows `c₂ < c₁` of column `c'`,
`stCoef(c₂) · R · w(c₁) ≤ stCoef(c₁) · w(c₂)` (the exponent drops by at least one). -/
theorem coef_ratio (R : ℕ) (hR : R % 2 = 1) (δ L : ℕ) (hL : sdLOK (taDesign s R) δ L) (rows : Fin s → ℕ → Fin s)
    (e1 e2 e3 u : ℚ) {c1 c2 c' : Fin s} (h1 : c1 ≠ c') (h2 : c2 ≠ c') (hlt : (c2 : ℕ) < c1) :
    (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c2 : ℚ) * R * taW s δ c1 c' ≤
      (stCoef (sdData (taDesign s R) δ L rows e1 e2 e3 u) c' c1 : ℚ) * taW s δ c2 c' := by
  sorry

end G1

section G2
variable {s : ℕ}

/-- **The geometric series of the proof of `thm:A`**: in a column whose rows all have the fraction `ε < ½`, with
positive steps, `μ_1 ≤ ε` and consecutive ratios `μ_{t+1} ≤ ρ μ_t`, `ρ(1 + ε) ≤ ε` (i.e. the steps differ by a
factor at least `1 + 1/ε`), every `N̄_{t-1} μ_t ≤ ε`. -/
theorem hier_geom (D : StagData s) (c' : Fin s) (ε ρ : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρε : ρ * (1 + ε) ≤ ε) (hlam : stLam (K := ℝ) D c' 0 = 2 * ε)
    (hpos : ∀ t < s - 1, 0 < stMu (K := ℝ) D c' t) (hμ0 : stMu (K := ℝ) D c' 0 ≤ ε)
    (hρ : ∀ t, t + 1 < s - 1 → stMu (K := ℝ) D c' (t + 1) ≤ ρ * stMu D c' t) :
    ∀ t, t + 1 < s - 1 → stNbar (K := ℝ) D c' t * stMu D c' (t + 1) ≤ ε := by
  sorry

/-- **`prop:P0`, consequence, at a natural threshold** (used by `thm:A` and the `s = 4, 5` designs): if `𝒫(p₀)`
holds at a natural number `p₀` exceeding the place differences, the numerators and denominators of the `Q_j` and
`L`, and `u < 1`, then for every prime `p ≥ p₀` the local roots of the frame (scale `θ = 2^δ L T`) exist, and for
every choice of them the conclusion of `P0_design` holds with `C'' = M⋆^+(p₀)`. -/
theorem P0_big (D : StagDesign s) (hs : 2 ≤ s) (hD : sdOK D) (δ L : ℕ) (hL : sdLOK D δ L)
    (rows : Fin s → ℕ → Fin s) (eCS eCC eSC u : ℚ) (hv : (sdData D δ L rows eCS eCC eSC u).Valid)
    (hu1 : u < 1) (p0 : ℕ) (hP0 : StP (sdData D δ L rows eCS eCC eSC u) (p0 : ℚ))
    (hba : ∀ b c : Fin s, |frameA D.fr b - frameA D.fr c| < p0)
    (hbQ : ∀ j, j ≠ D.cs → |(D.Q j).num| < p0 ∧ (D.Q j).den < p0) (hbL : L < p0)
    (p : ℕ) [Fact p.Prime] (hp : p0 ≤ p) :
    (∃ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) ∧
    ∀ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) →
      (∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) →
      (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) ≤ stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) ∧
      (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows eCS eCC eSC u) p) rule) ∧
      (∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows eCS eCC eSC u) p) rule →
        IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
          (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
          (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N
            (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))) ≤
            Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))))) ∧
      ∀ g : Fin s → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam D p δ c) →
        RespInS (ssGen g zθ) (stWin (sdData D δ L rows eCS eCC eSC u) p) →
        IsSeq0 (zcode p) (ssGen g zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
          (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
          (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
            Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) (p0 : ℝ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  sorry

end G2

section G3

theorem eps10_lt (s : ℕ) (hs : 3 ≤ s) : 1 / (10 * (s : ℝ)) < epsS s := by
  sorry

/-- **`thm:A`** (separation `1 - O(1/p)` in every dimension): for every `s ≥ 3` there are a staggered design on the
Faure places `(0, 1, …, s-1)` (staggered coordinate `0`, natural order of `C`, `Q_r = R^r` with an odd `R`), its
`δ`, `L` (the least values of `lem:R`), the row orders of decreasing steps, a uniform rational window fraction
`ε < ε_s`, a rational `u > 0` and a natural number `p₀` with `𝒫(p₀)` (an exact, decidable rational statement, so
`p₀(s)` is effectively computable; the design satisfies the limit hierarchy) such that for every prime `p ≥ p₀` (no
congruence condition) the local roots exist and, for every choice of them, the staggered rule (`def:BS`) gives:
selection rules exist, and every selection rule — and every multiplier family with the constants of `lem:R` and all
responses in the windows — gives a digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ 1 - C''_s/p` for every
`K ≥ 1`, `C''_s = M⋆^+(p₀)`, quasi-uniform (`h(P_{[N]}) ≤ (√s p/(1 - C''_s/p)) · 2δ(P_{[N]})`, `lem:prefix`). -/
theorem A (s : ℕ) (hs : 3 ≤ s) :
    ∃ (D : StagDesign s) (R δ L : ℕ) (rows : Fin s → ℕ → Fin s) (ε u : ℚ) (p0 : ℕ),
      D.fr = faureFr s ∧ (D.cs : ℕ) = 0 ∧ R % 2 = 1 ∧ (∀ j : Fin s, j ≠ D.cs → D.Q j = (R : ℚ) ^ (j : ℕ)) ∧
      sdOK D ∧ IsLeast {δ | sdDeltaOK D δ} δ ∧ IsLeast {L | sdLOK D δ L} L ∧
      0 < ε ∧ (ε : ℝ) < epsS s ∧ 0 < u ∧ (sdData D δ L rows ε ε ε u).Valid ∧
      (∀ c' : Fin s, ∀ t, t + 1 < s - 1 → stCoef (sdData D δ L rows ε ε ε u) c' (rows c' (t + 1)) < stCoef (sdData D δ L rows ε ε ε u) c' (rows c' t)) ∧
      LimHier (K := ℝ) (sdData D δ L rows ε ε ε u) ∧ StP (sdData D δ L rows ε ε ε u) (p0 : ℚ) ∧
      ∀ (p : ℕ) [Fact p.Prime], p0 ≤ p →
        (∃ zθ : Fin s → PowerSeries (ZMod p),
          (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) ∧
          ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) ∧
        ∀ zθ : Fin s → PowerSeries (ZMod p),
          (∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X) →
          (∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) →
          (stMv (sdData D δ L rows ε ε ε u) p D.cs : ℝ) ≤ stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) ∧
          (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
            IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows ε ε ε u) p) rule) ∧
          (∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
            IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows ε ε ε u) p) rule →
            IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
              (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
              (1 - (stMv (sdData D δ L rows ε ε ε u) p D.cs : ℝ) / p)) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
              (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
              (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p)) ∧
            ∀ N : ℕ, 2 ≤ N →
              Z3NetDGS.covRad euclDist (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))) ≤
                Real.sqrt s * p / (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p) *
                  (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                    (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))))) ∧
          ∀ g : Fin s → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam D p δ c) →
            RespInS (ssGen g zθ) (stWin (sdData D δ L rows ε ε ε u) p) →
            IsSeq0 (zcode p) (ssGen g zθ) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ)) (1 - (stMv (sdData D δ L rows ε ε ε u) p D.cs : ℝ) / p)) ∧
            (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ)) (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p)) ∧
            ∀ N : ℕ, 2 ≤ N →
              Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
                Real.sqrt s * p / (1 - stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ) / p) *
                  (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  sorry

end G3

section G4

/-- **The `s = 4` design** (`tab:BSdata`): `δ = 2` and `L = 3 581 577` are the least values of `lem:R`,
`g = (1, 612, -46818, 1591812)`, `u = (999/1000)(7/250)/|n_{3←0}|` with `n_{3←0}` the largest step of column `c⋆`,
and the stored rows (`taRows 4`) are the orders of strictly decreasing steps. -/
theorem A4_design :
    sdOK a4Design ∧ IsLeast {δ | sdDeltaOK a4Design δ} 2 ∧ IsLeast {L | sdLOK a4Design 2 L} 3581577 ∧
    (sdG a4Design 2 0 = 1 ∧ sdG a4Design 2 1 = 612 ∧ sdG a4Design 2 2 = -46818 ∧ sdG a4Design 2 3 = 1591812) ∧
    (∀ j : Fin 4, |sdN a4Design 2 3581577 j 0| ≤ |sdN a4Design 2 3581577 3 0|) ∧
    a4u = 999 / 1000 * (7 / 250) / |sdN a4Design 2 3581577 3 0| ∧
    (∀ c' : Fin 4, ∀ t < 2, stCoef a4Data c' (taRows 4 c' (t + 1)) < stCoef a4Data c' (taRows 4 c' t)) := by
  sorry

theorem a4Data_valid : a4Data.Valid := by
  sorry

/-- **The `s = 4` threshold** (`tab:BSdata`, `app:LFdata`): `𝒫(p₀)` at `p₀ = 14 314 526 192 182 751`,
`32044 < M⋆^+(p₀) < 32044.14`, and `𝒫(1.43·10^16)` fails. -/
theorem A4_threshold : StP a4Data (14314526192182751 : ℚ) ∧
    32044 < stMstP a4Data (14314526192182751 : ℚ) ∧ stMstP a4Data (14314526192182751 : ℚ) < 3204414 / 100 ∧
    ¬ StP a4Data (14300000000000000 : ℚ) := by
  sorry

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
  sorry

theorem a5Data_valid : a5Data.Valid := by
  sorry

/-- **The `s = 5` threshold** (`tab:BSdata`, `app:LFdata`): `𝒫(p₀)` at `p₀ = 1 978 313 734 082 584 379 393`, with
`2 722 234 324 < M⋆^+(p₀) < 2.72224·10^9`. -/
theorem A5_threshold : StP a5Data (1978313734082584379393 : ℚ) ∧
    2722234324 < stMstP a5Data (1978313734082584379393 : ℚ) ∧
    stMstP a5Data (1978313734082584379393 : ℚ) < 2722240000 := by
  sorry

end G4

section G5
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
  sorry

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
  sorry

end G5

end GeoSeq
