/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4OD
public import GeoSeq.V4ED
public import GeoSeq.V4Range
public import GeoSeq.V4Small
public import GeoSeq.V3Range
public import GeoSeq.V4Data3a

@[expose] public section

/-!
# GeoSeq stage V4: `thm:LF` for `s = 3` and the single primes

* **The archive** (`thm:LF`(a), `app:LFdata`, `tab:smallp`), `s = 3`: `LF_archive_s3` — every prime in `[13, 127)`
  has an archived ordered design valid at `p` (`odValid`), with `(p - Γ)/p > 0.1` and, from `31` on, `≥ 0.3`
  (kernel-checked data `lfChunk3a`, 25 records).
* **Every prime** (`thm:LF`(a) with `tab:LFY`), `s = 3`: `LF_a_s3` — for every prime `p ≥ 13` there is `Γ < p` with
  the thresholds of `tab:smallp`, coming from an archived ordered design or (above the archive) from the
  mixed-radix rule, and a quasi-uniform digital `(0,3)`-sequence over `𝔽_p` with `c(P_{3K}) ≥ (p - Γ)/p` for
  every `K`. (`s = 4`: `GeoSeq/V4LF4.lean`; `s = 5`: `GeoSeq/V4LF5.lean`.)
* **Single primes** (`thm:LF`(b)): `LF_b11`, `LF_b37` (`LB = 1/11`, `1/37`; exact coverings by enumeration).
  `p = 211` (`s = 5`) is not formalized (a computer-assisted remark, the research notes).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Helpers -/

lemma lb_gt_of {p Γ : ℕ} (hΓ : Γ < p) (h : p < 10 * (p - Γ)) : (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [lt_div_iff₀ hp0]
  have e : ((p - Γ : ℕ) : ℝ) = p - Γ := by push_cast [Nat.cast_sub hΓ.le]; ring
  have h' : (p : ℝ) < 10 * ((p - Γ : ℕ) : ℝ) := by exact_mod_cast h
  rw [e] at h'; linarith

lemma lb_ge_of {p Γ : ℕ} (hΓ : Γ < p) (h : 3 * p ≤ 10 * (p - Γ)) : (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [le_div_iff₀ hp0]
  have e : ((p - Γ : ℕ) : ℝ) = p - Γ := by push_cast [Nat.cast_sub hΓ.le]; ring
  have h' : 3 * (p : ℝ) ≤ 10 * ((p - Γ : ℕ) : ℝ) := by exact_mod_cast h
  rw [e] at h'; linarith

/-- The mixed-radix rule gives the sequence (`thm:MR` with the step factors of the rule). -/
lemma mr_rule_seq (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hsp : s ≤ p) (hΓ : mrCost s p (mrRuleH s p) < p) :
    ∃ C : Gen s (ZMod p), IsSeq0 (zcode p) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) C)
        (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
          Real.sqrt s * p / (((p : ℝ) - mrCost s p (mrRuleH s p)) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  obtain ⟨zθ, hroot, hplace⟩ := faure_roots_exist s p hsp (mrTheta s p)
  obtain ⟨⟨rule, hrule⟩, hall⟩ :=
    MR s p hs hsp (mrRuleH s p) (fun t _ _ => le_max_left _ _) hΓ zθ hroot hplace
  exact ⟨_, hall rule hrule⟩

/-- **`thm:LF`(a), archive, `s = 3`**: every prime `13 ≤ p < 127` has an archived ordered design valid at
`p`, with `(p - Γ)/p > 1/10` and, from `31` on, `(p - Γ)/p ≥ 3/10` (integer forms). -/
theorem LF_archive_s3 (p : ℕ) (hp : p.Prime) (h1 : 13 ≤ p) (h2 : p < 127) :
    ∃ D : ODesign 3, odValid p D ∧ p < 10 * (p - odCost D p) ∧
      (31 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  obtain ⟨D, hv, hy1, hy3⟩ := lfOK_sound _ _ _ _ _ _ lfChunk3a p hp h1 (by omega)
  exact ⟨D, hv, hy1 h1, hy3⟩

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
  have hp := hpf.out
  by_cases hlt : p < 127
  · obtain ⟨D, hv, hy1, hy3⟩ := LF_archive_s3 p hp h13 hlt
    have hΓ := hv.2.2.2.2.2.2
    exact ⟨odCost D p, hΓ, lb_gt_of hΓ hy1, fun h => lb_ge_of hΓ (hy3 h), Or.inl ⟨D, hv, rfl⟩,
      by exact_mod_cast od_seq D (by norm_num) hv⟩
  · have hΓ := MR_every_prime_s3 p hp (by omega)
    have h127 : (127 : ℝ) ≤ p := by exact_mod_cast (show 127 ≤ p by omega)
    have h3 := tabLFY.2.1 p hp (by linarith)
    refine ⟨_, hΓ, by linarith, fun _ => h3.le, Or.inr rfl, ?_⟩
    exact_mod_cast mr_rule_seq 3 p le_rfl (by omega) hΓ

/-! ## Single primes -/

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
  obtain ⟨hv, hc⟩ := edP11_valid
  obtain ⟨C, h1, h2, h3⟩ := ed_seq edP11 (by norm_num) (by norm_num) hv
  rw [hc] at h2 h3
  refine ⟨hv, hc, C, h1, fun K hK => ?_, fun N hN => ?_⟩
  · have := h2 K hK; norm_num at this ⊢; exact this
  · have := h3 N hN; norm_num at this ⊢; exact this

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
  obtain ⟨hv, hc⟩ := edP37_valid
  obtain ⟨C, h1, h2, h3⟩ := ed_seq edP37 (by norm_num) (by norm_num) hv
  rw [hc] at h2 h3
  refine ⟨hv, hc, C, h1, fun K hK => ?_, fun N hN => ?_⟩
  · have := h2 K hK; norm_num at this ⊢; exact this
  · have := h3 N hN; norm_num at this ⊢; exact this

end GeoSeq
