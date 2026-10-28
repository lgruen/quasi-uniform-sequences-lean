/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4LF3
public import GeoSeq.V4Data5a
public import GeoSeq.V4Data5b
public import GeoSeq.V4Data5c
public import GeoSeq.V4Data5d
public import GeoSeq.V4Data5e
public import GeoSeq.V4Data5f
public import GeoSeq.V4Data5g
public import GeoSeq.V4Data5h
public import GeoSeq.V4Data5i
public import GeoSeq.V4Data5j

@[expose] public section

/-!
# GeoSeq stage V4: `thm:LF`(a) for `s = 5`

`LF_archive_s5` (every prime in `[269, 20873)` has a valid archived ordered design with the thresholds of `tab:smallp`;
kernel-checked data `lfChunk5*`) and `LF_a_s5` (every prime `≥ 269`, with the mixed-radix rule above the archive).
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`thm:LF`(a), archive, `s = 5`**: every prime `269 ≤ p < 20873` has an archived ordered design valid at
`p`, with `(p - Γ)/p > 1/10` from `373` on and `(p - Γ)/p ≥ 3/10` from `1277` on. -/
theorem LF_archive_s5 (p : ℕ) (hp : p.Prime) (h1 : 269 ≤ p) (h2 : p < 20873) :
    ∃ D : ODesign 5, odValid p D ∧ (373 ≤ p → p < 10 * (p - odCost D p)) ∧
      (1277 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  by_cases c : p < 2336
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5a p hp h1 (by omega)
  by_cases c : p < 4403
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5b p hp (by omega) (by omega)
  by_cases c : p < 6470
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5c p hp (by omega) (by omega)
  by_cases c : p < 8537
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5d p hp (by omega) (by omega)
  by_cases c : p < 10604
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5e p hp (by omega) (by omega)
  by_cases c : p < 12671
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5f p hp (by omega) (by omega)
  by_cases c : p < 14738
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5g p hp (by omega) (by omega)
  by_cases c : p < 16805
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5h p hp (by omega) (by omega)
  by_cases c : p < 18872
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5i p hp (by omega) (by omega)
  · exact lfOK_sound _ _ _ _ _ _ lfChunk5j p hp (by omega) (by omega)

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
  have hp := hpf.out
  by_cases hlt : p < 20873
  · obtain ⟨D, hv, hy1, hy3⟩ := LF_archive_s5 p hp h269 hlt
    have hΓ := hv.2.2.2.2.2.2
    exact ⟨odCost D p, hΓ, fun h => lb_gt_of hΓ (hy1 h), fun h => lb_ge_of hΓ (hy3 h),
      Or.inl ⟨D, hv, rfl⟩, by exact_mod_cast od_seq D (by norm_num) hv⟩
  · have hΓ := MR_every_prime_s5 p hp (by omega)
    have h0 : (20873 : ℝ) ≤ p := by exact_mod_cast (show 20873 ≤ p by omega)
    have h3 := tabLFY.2.2.2.2.2 p hp (by linarith)
    refine ⟨_, hΓ, fun _ => by linarith, fun _ => h3.le, Or.inr rfl, ?_⟩
    exact_mod_cast mr_rule_seq 5 p (by norm_num) (by omega) hΓ

end GeoSeq
