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
# Statements: stage V4s5 (`thm:LF`, small primes)

`thm:LF`(a) for `s = 5` (archive `[269, 20873)`, kernel-checked data, and every prime `≥ 269`).
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

/-- **`thm:LF`(a), archive, `s = 5`**: every prime `269 ≤ p < 20873` has an archived ordered design valid at
`p`, with `(p - Γ)/p > 1/10` from `373` on and `(p - Γ)/p ≥ 3/10` from `1277` on. -/
theorem LF_archive_s5 (p : ℕ) (hp : p.Prime) (h1 : 269 ≤ p) (h2 : p < 20873) :
    ∃ D : ODesign 5, odValid p D ∧ (373 ≤ p → p < 10 * (p - odCost D p)) ∧
      (1277 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  sorry

/-- **`thm:LF`(a), `s = 5`, every prime `p ≥ 269`**: there is `Γ < p`, with `(p - Γ)/p > 1/10` from `373` on
and `(p - Γ)/p ≥ 3/10` from `1277` on, which is the cost of an archived ordered design valid at `p` or (above
the archive, `p ≥ 20873`) of the mixed-radix rule, and a quasi-uniform digital `(0,5)`-sequence over `𝔽_p`
with `c(P_{5K}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem LF_a_s5 (p : ℕ) [hpf : Fact p.Prime] (h269 : 269 ≤ p) :
    ∃ Γ : ℕ, Γ < p ∧ (373 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (1277 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧
      ((∃ D : ODesign 5, odValid p D ∧ odCost D p = Γ) ∨ Γ = mrCost 5 p (mrRuleH 5 p)) ∧
      ∃ C : Gen 5 (ZMod p), IsSeq0 (zcode p) C ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 5 K (seqPoint (zcode p) C) (((p : ℝ) - Γ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
            Real.sqrt 5 * p / (((p : ℝ) - Γ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  sorry

end G0

end GeoSeq
