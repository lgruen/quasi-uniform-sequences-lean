/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4LF3
public import GeoSeq.V4Data4a
public import GeoSeq.V4Data4b
public import GeoSeq.V4Data4c

@[expose] public section

/-!
# GeoSeq stage V4: `thm:LF`(a) for `s = 4`

`LF_archive_s4` (every prime in `[47, 1931)` has a valid archived ordered design with the thresholds of `tab:smallp`;
kernel-checked data `lfChunk4*`) and `LF_a_s4` (every prime `≥ 47`, with the mixed-radix rule above the archive).
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`thm:LF`(a), archive, `s = 4`**: every prime `47 ≤ p < 1931` has an archived ordered design valid at
`p`, with `(p - Γ)/p > 1/10` from `67` on and `(p - Γ)/p ≥ 3/10` from `163` on. -/
theorem LF_archive_s4 (p : ℕ) (hp : p.Prime) (h1 : 47 ≤ p) (h2 : p < 1931) :
    ∃ D : ODesign 4, odValid p D ∧ (67 ≤ p → p < 10 * (p - odCost D p)) ∧
      (163 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  by_cases c1 : p < 700
  · exact lfOK_sound _ _ _ _ _ _ lfChunk4a p hp h1 (by omega)
  by_cases c2 : p < 1400
  · exact lfOK_sound _ _ _ _ _ _ lfChunk4b p hp (by omega) (by omega)
  · exact lfOK_sound _ _ _ _ _ _ lfChunk4c p hp (by omega) (by omega)

/-- **`thm:LF`(a), `s = 4`, every prime `p ≥ 47`**: there is `Γ < p`, with `(p - Γ)/p > 1/10` from `67` on
and `(p - Γ)/p ≥ 3/10` from `163` on, which is the cost of an archived ordered design valid at `p` or (above
the archive, `p ≥ 1931`) of the mixed-radix rule, and a quasi-uniform digital `(0,4)`-sequence over `𝔽_p`
with `c(P_{4K}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem LF_a_s4 (p : ℕ) [hpf : Fact p.Prime] (h47 : 47 ≤ p) :
    ∃ Γ : ℕ, Γ < p ∧ (67 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (163 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧
      ((∃ D : ODesign 4, odValid p D ∧ odCost D p = Γ) ∨ Γ = mrCost 4 p (mrRuleH 4 p)) ∧
      ∃ C : Gen 4 (ZMod p), IsSeq0 (zcode p) C ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 4 K (seqPoint (zcode p) C) (((p : ℝ) - Γ) / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
            Real.sqrt 4 * p / (((p : ℝ) - Γ) / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  have hp := hpf.out
  by_cases hlt : p < 1931
  · obtain ⟨D, hv, hy1, hy3⟩ := LF_archive_s4 p hp h47 hlt
    have hΓ := hv.2.2.2.2.2.2
    exact ⟨odCost D p, hΓ, fun h => lb_gt_of hΓ (hy1 h), fun h => lb_ge_of hΓ (hy3 h),
      Or.inl ⟨D, hv, rfl⟩, by exact_mod_cast od_seq D (by norm_num) hv⟩
  · have hΓ := MR_every_prime_s4 p hp (by omega)
    have h0 : (1931 : ℝ) ≤ p := by exact_mod_cast (show 1931 ≤ p by omega)
    have h3 := tabLFY.2.2.2.1 p hp (by linarith)
    refine ⟨_, hΓ, fun _ => by linarith, fun _ => h3.le, Or.inr rfl, ?_⟩
    exact_mod_cast mr_rule_seq 4 p (by norm_num) (by omega) hΓ

end GeoSeq
