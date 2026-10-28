/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4Defs
public import GeoSeq.V3Defs

@[expose] public section

/-!
# Statements: stage V4 (`thm:LF`, small primes)

The ordered-window theorem over integer frames, ordered designs (`thm:LF`(a)) with the archive check, `s = 3` (archive `[13, 127)` and every prime `≥ 13`), and the single-prime designs `p = 11`, `37` (`thm:LF`(b)).
PROVED (`GeoSeq/V4Core.lean`, `GeoSeq/V4OD.lean`, `GeoSeq/V4ED.lean`, `GeoSeq/V4Range.lean`, `GeoSeq/V4LF3/4/5.lean`;
kernel checks `GeoSeq/V4Data*.lean`, `GeoSeq/V4Small.lean`); generated verbatim from the proof files' signatures by
`scripts/gen_v4_statements.py` (definitions in `GeoSeq/V4Defs.lean`).
Paper: V3 (development version V3 of the paper, `05-order.tex`, `E-designs.tex`); label → Lean map in
the formalization notes of the research repository, review the statement-review notes of the research repository.
-/

namespace GeoSeq
open Finset PowerSeries
open scoped Polynomial

section G0
variable {p : ℕ} [Fact p.Prime]

/-- **The local roots of an integer frame exist** (places distinct mod `p`, any scale `θ`). -/
theorem frame_roots_exist (p s : ℕ) [Fact p.Prime] (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0) (θ : ZMod p) :
    ∃ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p s fr) = C θ * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p) := by
  sorry

/-- `w'(a_c) = ∏_{b≠c} (a_c - a_b)` for an integer frame. -/
theorem frame_placeDer (s : ℕ) (fr : List ℤ) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p)) (c : Fin s) :
    placeDer zθ c = ((frameW s fr c : ℤ) : ZMod p) := by
  sorry

end G0

section G1
variable {s : ℕ}

/-- **The ordered-window theorem** (the argument of `thm:MR` for any ordered windows; `thm:LF`). Let
`p ≥ 5` be prime, `w = ∏_{c<s} (z - a_c)` an integer frame with places distinct mod `p`, local roots
`z_c(θx)`, a scale `θ ≠ 0` and constants `λ_c ≠ 0`. Suppose the upper crosses are integers,
`κ_{c←j} = κ̂_{c←j}` (`c < j`), with `|κ̂_{c←j}| ≤ B_{c←j}` (condition (i)), the integer conditions of
`def:lex` hold, `Γ = max_c (A_c + M_c + B_c) < p`, and every column covers in the second form of
`lem:lexcover` (for every `σ` some own value `o ∈ [-(A_j+M_j-1), -A_j]` has `σ_c + o κ̂_{c←j} ∈ [-B_{c←j},
B_{c←j}]` for every `c < j`). Then selection rules exist, and every selection rule defines a quasi-uniform
digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem lex_sound (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hs : 1 ≤ s) (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0)
    (θ : ZMod p) (hθ : θ ≠ 0) (lamv : Fin s → ZMod p) (hlam : ∀ c, lamv c ≠ 0)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s fr) = C θ * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p))
    (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (hlex : IsLexData p A M Bx)
    (hcost : lexCost A M Bx < p) (κ : Fin s → Fin s → ℤ)
    (hκ : ∀ c j, c < j → kapL θ lamv zθ c j = (κ c j : ZMod p))
    (hi : ∀ c j, c < j → (κ c j).natAbs ≤ Bx c j)
    (hcov : ∀ j : Fin s, ∀ σ : Fin s → ZMod p, ∃ o : ℤ, -((A j : ℤ) + M j - 1) ≤ o ∧ o ≤ -(A j : ℤ) ∧
      ∀ c, c < j → σ c + (o : ZMod p) * (κ c j : ZMod p) ∈ intWin p (-(Bx c j : ℤ)) (Bx c j)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (lexWin p A M Bx) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (lexWin p A M Bx) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))
        (((p : ℝ) - lexCost A M Bx) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - lexCost A M Bx) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ)))) := by
  sorry

end G1

section G2
variable {s : ℕ}
variable {p : ℕ} [Fact p.Prime]

/-- **The crosses of an ordered design** (`lem:cauchy`): with `λ_c = θ^c/Q_{0c}`, the upper crosses are the
integers `κ_{c←j} = odK D c j`. -/
theorem od_kap (D : ODesign s) (hv : odValid p D) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.frame c : ℤ) : ZMod p)) (c j : Fin s) (hcj : c < j) :
    kapL (odTheta D p) (odLam D p) zθ c j = (odK D c j : ZMod p) := by
  sorry

/-- **The coverings of an ordered design** (`lem:ws` in the stored row order, `lem:lexcover` second form). -/
theorem od_cover (D : ODesign s) (hv : odValid p D) (j : Fin s) (σ : Fin s → ZMod p) :
    ∃ o : ℤ, -((odB D p j : ℤ) + odM D p j - 1) ≤ o ∧ o ≤ -(odB D p j : ℤ) ∧
      ∀ c : Fin s, c < j → σ c + (o : ZMod p) * (odK D c j : ZMod p) ∈
        intWin p (-(odBx D p c j : ℤ)) (odBx D p c j) := by
  sorry

/-- **`thm:MR` for ordered designs** (`thm:LF`, `app:LFdata`: "Theorem MR holds verbatim"). Let `s ≥ 2`,
`p` prime and `D` an ordered design valid at `p` (`odValid`: row orders, places distinct mod `p`, `θ` prime to
`p`, positive superdiagonal prime to `p`, integral nonzero upper triangle, `Γ < p`). For every choice of the
local roots `z_c(θx)` of the frame (`w(z_c(θx)) = θx`, `z_c(0) = a_c`), with the constants `λ_c = θ^c/Q_{0c}`
and the windows of `lem:ws` in the stored row order, selection rules exist, and every selection rule defines
a digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`, quasi-uniform:
`h(P_{[N]}) ≤ (√s p/((p - Γ)/p)) δ(P_{[N]})` for every `N ≥ 2` (`lem:prefix`). -/
theorem od_sound (D : ODesign s) (hs : 2 ≤ s) (hv : odValid p D) (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s D.frame) = C (odTheta D p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.frame c : ℤ) : ZMod p)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (odTheta D p) (odLam D p) zθ (odWin D p) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (odTheta D p) (odLam D p) zθ (odWin D p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ))
        (((p : ℝ) - odCost D p) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - odCost D p) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ)))) := by
  sorry

/-- **A valid ordered design gives a sequence** (`thm:LF`(a), existential form): a quasi-uniform digital
`(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem od_seq (D : ODesign s) (hs : 2 ≤ s) (hv : odValid p D) :
    ∃ C : Gen s (ZMod p), IsSeq0 (zcode p) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) C) (((p : ℝ) - odCost D p) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
          Real.sqrt s * p / (((p : ℝ) - odCost D p) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  sorry

end G2

section G3
variable {s : ℕ}
variable {p : ℕ} [Fact p.Prime]

/-- **The crosses of explicit ordered windows** are the stored integers. -/
theorem ed_kap (E : EDesign s) (hv : edValid p E) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA E.frame c : ℤ) : ZMod p)) (c j : Fin s) (hcj : c < j) :
    kapL (edTheta E p) (edLam E p) zθ c j = (edK E c j : ZMod p) := by
  sorry

/-- **Explicit ordered windows** (`thm:LF`(b)): if `edValid p E` (`s ≥ 1`, `p ≥ 5`), then for every choice of
the local roots selection rules exist, and every selection rule defines a quasi-uniform digital
`(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`, `Γ = edCost E`. -/
theorem ed_sound (E : EDesign s) (hs : 1 ≤ s) (hp : 5 ≤ p) (hv : edValid p E)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s E.frame) = C (edTheta E p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA E.frame c : ℤ) : ZMod p)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (edTheta E p) (edLam E p) zθ (edWin E p) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (edTheta E p) (edLam E p) zθ (edWin E p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ))
        (((p : ℝ) - edCost E) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - edCost E) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ)))) := by
  sorry

/-- **Explicit ordered windows give a sequence** (existential form of `ed_sound`). -/
theorem ed_seq (E : EDesign s) (hs : 1 ≤ s) (hp : 5 ≤ p) (hv : edValid p E) :
    ∃ C : Gen s (ZMod p), IsSeq0 (zcode p) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) C) (((p : ℝ) - edCost E) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
          Real.sqrt s * p / (((p : ℝ) - edCost E) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  sorry

end G3

section G4
variable {s : ℕ}

/-- **Soundness of the archive check**: every prime of the range has a valid archived ordered design with
the two thresholds. -/
theorem lfOK_sound (lo len B y1 y3 : ℕ) (recs : List (ODRec s)) (h : lfOK lo len B y1 y3 recs = true)
    (p : ℕ) (hp : p.Prime) (h1 : lo ≤ p) (h2 : p < lo + len) :
    ∃ D : ODesign s, odValid p D ∧ (y1 ≤ p → p < 10 * (p - odCost D p)) ∧
      (y3 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  sorry

end G4

section G5

/-- **`thm:LF`(a), archive, `s = 3`**: every prime `13 ≤ p < 127` has an archived ordered design valid at
`p`, with `(p - Γ)/p > 1/10` and, from `31` on, `(p - Γ)/p ≥ 3/10` (integer forms). -/
theorem LF_archive_s3 (p : ℕ) (hp : p.Prime) (h1 : 13 ≤ p) (h2 : p < 127) :
    ∃ D : ODesign 3, odValid p D ∧ p < 10 * (p - odCost D p) ∧
      (31 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  sorry

/-- **`thm:LF`(a), `s = 3`, every prime `p ≥ 13`** (with `tab:smallp`, `tab:LFY`): there is `Γ < p` with
`(p - Γ)/p > 1/10` and, from `31` on, `(p - Γ)/p ≥ 3/10`, which is the cost of an archived ordered design
valid at `p` or (above the archive, `p ≥ 127`) of the mixed-radix rule, and a quasi-uniform digital
`(0,3)`-sequence over `𝔽_p` with `c(P_{3K}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem LF_a_s3 (p : ℕ) [hpf : Fact p.Prime] (h13 : 13 ≤ p) :
    ∃ Γ : ℕ, Γ < p ∧ (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p ∧ (31 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧
      ((∃ D : ODesign 3, odValid p D ∧ odCost D p = Γ) ∨ Γ = mrCost 3 p (mrRuleH 3 p)) ∧
      ∃ C : Gen 3 (ZMod p), IsSeq0 (zcode p) C ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K (seqPoint (zcode p) C) (((p : ℝ) - Γ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
            Real.sqrt 3 * p / (((p : ℝ) - Γ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  sorry

/-- **`thm:LF`(b), `p = 11`** (`s = 3`): the explicit ordered windows `edP11` of `app:LFdata` (Faure frame,
`θ = 5`, `λ = (1,4,2)`, crosses `(2,2,1)`, `Γ = 10`) are valid with exact coverings, and give a quasi-uniform
digital `(0,3)`-sequence over `𝔽_11` with `c(P_{3K}) ≥ 1/11` for every `K ≥ 1`. -/
theorem LF_b11 : edValid 11 edP11 ∧ edCost edP11 = 10 ∧
    ∃ C : Gen 3 (ZMod 11), IsSeq0 (zcode 11) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel 11 3 K (seqPoint (zcode 11) C) (1 / 11)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 11) C)) ≤
          Real.sqrt 3 * 11 / (1 / 11) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 11) C))) := by
  sorry

/-- **`thm:LF`(b), `p = 37`** (`s = 4`): the explicit ordered windows `edP37` (`lex_witnesses/smallp`,
`Γ = 36`) are valid with exact coverings, and give a quasi-uniform digital `(0,4)`-sequence over `𝔽_37` with
`c(P_{4K}) ≥ 1/37` for every `K ≥ 1`. -/
theorem LF_b37 : edValid 37 edP37 ∧ edCost edP37 = 36 ∧
    ∃ C : Gen 4 (ZMod 37), IsSeq0 (zcode 37) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel 37 4 K (seqPoint (zcode 37) C) (1 / 37)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 37) C)) ≤
          Real.sqrt 4 * 37 / (1 / 37) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 37) C))) := by
  sorry

end G5

end GeoSeq
