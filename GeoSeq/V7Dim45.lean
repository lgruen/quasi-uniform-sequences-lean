/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7Dim
public import GeoSeq.V4LF4
public import GeoSeq.V4LF5
public import GeoSeq.V6A
public import GeoSeq.S4Cert

@[expose] public section

/-!
# GeoSeq stage V7: dimensions four and higher (`thm:dim45`, `tab:dim45`)

* **`dim45_primes`**: the prime-base parts of `thm:dim45`: (a) `s = 4`: `p = 37` (`1/37`, `thm:LF`(b)), every prime
  `p ≥ 47` (`thm:LF`(a)); (b) `s = 5`: every prime `p ≥ 269` (`thm:LF`(a)); in addition (not part of `thm:dim45`,
  which defers it to `rem:p211`) `p = 211` (`2/211`) under the explicit hypothesis that the coverings of columns
  `3` and `4` of `edP211` hold (the computer-assisted part, `≈ 10^9` kernel steps; all other conditions of
  `edValid` are kernel-checked); (c) `s = 6, 7`: every prime
  `p ≥ 8.607·10^5`, `p ≥ 5.322·10^7` (proved, `thm:MRall` + `tab:P1`), and every prime `p ≥ 281 053`,
  `p ≥ 14 642 759` under the explicit hypothesis `Γ < p` at the primes in between (the computer-assisted range of
  `tab:P1`; measured: `≈ 7.5 ms` per integer in the Lean kernel, `≈ 72 min` for `s = 6`, not run); (d) every `s ≥ 3`:
  every prime `p > max(p_1(s), s)` (`thm:MRall`(b)), the bound `1 - C'_s p^{-1/s}` for `p ≥ max(Q_s^s u^{*s}, s)`
  (`thm:MRall`(c), any real `u^* > u_min` with `F(u^*) < 1`), and every prime `p ≥ p_0(s)` with `1 - C''_s/p`
  (`thm:A`).
* **`dim45_of_small`** (`q = 4`, `s = 4` from the statements `S4_net`, `S4_sep` of `thm:S4`, which are compared in
  `comparatorGeoSeqS4.json`, replay ≈ 11 min), **`dim45_q4`** (unconditional), **`dim45`** (`thm:dim45`, unconditional:
  `dim45_q4` and `dim45_primes`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

/-- The conditions of `edValid` at `p = 211` other than the coverings of columns `3` and `4` (kernel-checked), and
`Γ = 209` (`rem:p211`). -/
theorem edP211_valid (h3 : edCover 211 edP211 3 = true) (h4 : edCover 211 edP211 4 = true) :
    edValid 211 edP211 ∧ edCost edP211 = 209 := by
  have c0 : edCover 211 edP211 0 = true := by decide +kernel
  have c1 : edCover 211 edP211 1 = true := by decide +kernel
  have c2 : edCover 211 edP211 2 = true := by decide +kernel
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fun j hj => ?_⟩, by decide +kernel⟩
  interval_cases j
  · exact c0
  · exact c1
  · exact c2
  · exact h3
  · exact h4

/-- The mixed-radix rule gives `QUSep` whenever `Γ < p` (`thm:MR` on the Faure frame with the rule's step factors). -/
lemma mr_qusep (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hsp : s ≤ p) (hΓ : mrCost s p (mrRuleH s p) < p) :
    ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p) := by
  obtain ⟨C, hseq, hsep, -⟩ := mr_rule_seq s p hs hsp hΓ
  exact ⟨C, qusep_of (zcode p) C (by have := (Fact.out : p.Prime).two_le; omega) (by omega) hseq _
    (lb_pos hΓ) hsep⟩

/-- **`thm:dim45`, the prime bases** (`tab:dim45`): (a) `s = 4`: `p = 37` (`1/37`) and every prime `p ≥ 47` (`thm:LF`);
(b) `s = 5`: every prime `p ≥ 269` (`thm:LF`); (c) `s = 6`, `s = 7`: every prime `p ≥ 8.607·10^5` resp. `p ≥ 5.322·10^7` (mixed-radix
rule, `thm:MRall`, `tab:P1`), and every prime `p ≥ 281 053` resp. `p ≥ 14 642 759` given `Γ < p` at every prime in
between (hypothesis: the computer-assisted range of `tab:P1`); (d) every `s ≥ 3`: every prime `p > max(p_1(s), s)`,
with `c(P_{sK}) ≥ 1 - C'_s p^{-1/s}` for `p ≥ max(Q_s^s u^{*s}, s)` for any real `u^* > u_min` with `F(u^*) < 1`
(`thm:MRall`), and every prime `p ≥ p_0(s)` with `c(P_{sK}) ≥ 1 - C''_s/p` (`thm:A`). Each: a quasi-uniform digital
`(0,s)`-sequence with the bound on `c(P_{sK})` for every `K ≥ 1`. The Lean statement additionally carries the
conditional conjunct `p = 211`, `s = 5` (`2/211`; hypothesis: the coverings of columns `3`, `4` of the explicit
windows `edP211`), which is `rem:p211` — stronger than the theorem, with the covering hypothesis explicit. -/
theorem dim45_primes :
    (∃ C : Gen 4 (ZMod 37), QUSep (zcode 37) 4 C (1 / 37)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 47 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (67 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (163 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 4 (ZMod p), QUSep (zcode p) 4 C (((p : ℝ) - Γ) / p)) ∧
    (edCover 211 edP211 3 = true → edCover 211 edP211 4 = true →
      edValid 211 edP211 ∧ edCost edP211 = 209 ∧ ∃ C : Gen 5 (ZMod 211), QUSep (zcode 211) 5 C (2 / 211)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 269 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (373 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (1277 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 5 (ZMod p), QUSep (zcode p) 5 C (((p : ℝ) - Γ) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 860700 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
      ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 281053 ≤ p → p < 860700 → mrCost 6 p (mrRuleH 6 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 281053 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
        ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 53220000 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
      ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 14642759 ≤ p → p < 53220000 → mrCost 7 p (mrRuleH 7 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 14642759 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
        ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ (p : ℕ) [Fact p.Prime], mrP1 s < p → s < p → mrCost s p (mrRuleH s p) < p ∧
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ us : ℝ, (mrUmin s : ℝ) < us → mrF s us < 1 →
      ∀ (p : ℕ) [Fact p.Prime], (mrQss s : ℝ) * us ^ s ≤ p → s ≤ p → mrCost s p (mrRuleH s p) < p ∧
        1 - mrCp s us * (p : ℝ) ^ (-(1 : ℝ) / s) ≤ ((p : ℝ) - mrCost s p (mrRuleH s p)) / p ∧
        ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∃ (p0 : ℕ) (C'' : ℝ), ∀ (p : ℕ) [Fact p.Prime], p0 ≤ p →
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (1 - C'' / p)) := by
  have h6 : ∀ (p : ℕ) [Fact p.Prime], 860700 ≤ p → mrCost 6 p (mrRuleH 6 p) < p := fun p hp h => by
    refine (tabP1_s6.2.2.2.2.2.2 p hp.out ?_).1
    have : (860700 : ℝ) ≤ p := by exact_mod_cast h
    push_cast; linarith
  have h7 : ∀ (p : ℕ) [Fact p.Prime], 53220000 ≤ p → mrCost 7 p (mrRuleH 7 p) < p := fun p hp h => by
    refine (tabP1_s7.2.2.2.2.2.2 p hp.out ?_).1
    have : (53220000 : ℝ) ≤ p := by exact_mod_cast h
    push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, fun p _ h => ⟨h6 p h, mr_qusep 6 p (by norm_num) (by omega) (h6 p h)⟩,
    fun H p hp h => ?_, fun p _ h => ⟨h7 p h, mr_qusep 7 p (by norm_num) (by omega) (h7 p h)⟩,
    fun H p hp h => ?_, fun s hs p _ hp1 hsp => ?_, fun s hs us hus hF p _ hP hsp => ?_, fun s hs => ?_⟩
  · obtain ⟨-, -, C, hseq, hsep, -⟩ := LF_b37
    exact ⟨C, qusep_of (zcode 37) C (by norm_num) (by norm_num) hseq _ (by norm_num) hsep⟩
  · intro p hp h47
    obtain ⟨Γ, hΓ, h1, h3, -, C, hseq, hsep, -⟩ := LF_a_s4 p h47
    exact ⟨Γ, hΓ, h1, h3, C, qusep_of (zcode p) C (by omega) (by norm_num) hseq _ (lb_pos hΓ) hsep⟩
  · intro h3 h4
    obtain ⟨hv, hc⟩ := edP211_valid h3 h4
    obtain ⟨C, hseq, hsep, -⟩ := ed_seq edP211 (by norm_num) (by norm_num) hv
    rw [hc] at hsep
    have e : ((211 : ℕ) : ℝ) - ((209 : ℕ) : ℝ) = 2 := by norm_num
    refine ⟨hv, hc, C, qusep_of (zcode 211) C (by norm_num) (by norm_num) hseq _ (by norm_num) ?_⟩
    intro K hK
    have := hsep K hK
    rw [e] at this
    exact this
  · intro p hp h269
    obtain ⟨Γ, hΓ, h1, h3, -, C, hseq, hsep, -⟩ := LF_a_s5 p h269
    exact ⟨Γ, hΓ, h1, h3, C, qusep_of (zcode p) C (by omega) (by norm_num) hseq _ (lb_pos hΓ) hsep⟩
  · have hΓ : mrCost 6 p (mrRuleH 6 p) < p := by
      by_cases hb : p < 860700
      · exact H p hp.out h hb
      · exact h6 p (by omega)
    exact ⟨hΓ, mr_qusep 6 p (by norm_num) (by omega) hΓ⟩
  · have hΓ : mrCost 7 p (mrRuleH 7 p) < p := by
      by_cases hb : p < 53220000
      · exact H p hp.out h hb
      · exact h7 p (by omega)
    exact ⟨hΓ, mr_qusep 7 p (by norm_num) (by omega) hΓ⟩
  · have hΓ := (MRall_b s p hs hp1 hsp).1
    exact ⟨hΓ, mr_qusep s p hs hsp.le hΓ⟩
  · obtain ⟨hΓ, he, hle⟩ := MRall_c s p hs us hus hF hP hsp
    refine ⟨hΓ, by linarith, mr_qusep s p hs hsp hΓ⟩
  · obtain ⟨D, R, δ, L, rows, ε, u, p0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ := A s hs
    refine ⟨p0, stMstP (sdData D δ L rows ε ε ε u) (p0 : ℝ), fun p _ hp0 => ?_⟩
    obtain ⟨⟨zθ, hroot, hplace⟩, hz⟩ := hall p hp0
    obtain ⟨-, ⟨rule, hrule⟩, hrules, -⟩ := hz zθ hroot hplace
    obtain ⟨hseq, -, hsep, hmesh⟩ := hrules rule hrule
    exact ⟨_, hseq, hsep, hmesh⟩

lemma s4_lb : (3013 / 100000 : ℝ) ≤ Real.sqrt 952 / 1024 := by
  rw [le_div_iff₀ (by norm_num)]
  exact Real.le_sqrt_of_sq_le (by norm_num)

/-- **`thm:dim45` from `thm:S4`**: given the statements `S4_net`, `S4_sep` of `thm:S4`, part (a) `q = 4`
(`c(P_{4K}) ≥ 0.03013`) together with all prime-base parts `dim45_primes`. -/
theorem dim45_of_small (hS4n : IsSeq0 f4code S4gen)
    (hS4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 4 K (seqPoint f4code S4gen) (Real.sqrt 952 / 1024)) :
    QUSep f4code 4 S4gen (3013 / 100000) :=
  qusep_of f4code S4gen (by norm_num) (by norm_num) hS4n _ (by norm_num)
    fun K hK => sepAtLevel_mono _ s4_lb (hS4s K hK)

/-- **`thm:dim45`, part (a) `q = 4`** (unconditional; `thm:S4`): a quasi-uniform digital `(0,4)`-sequence over `𝔽_4`
(the sequence `S4gen` of `thm:S4`) with `c(P_{4K}) ≥ 0.03013` for every `K ≥ 1`. With `dim45_primes` this is `thm:dim45`. -/
theorem dim45_q4 : QUSep f4code 4 S4gen (3013 / 100000) :=
  dim45_of_small S4_net S4_sep

/-- **`thm:dim45`** (dimensions four and higher; `tab:dim45`): quasi-uniform digital `(0,s)`-sequences with explicit
bounds on `c(P_{sK})` for every `K ≥ 1`: (a) `s = 4`: `q = 4` (the sequence `S4gen` of `thm:S4`, `0.03013`), `p = 37` (`1/37`), every prime
`p ≥ 47`; (b) `s = 5`: every prime `p ≥ 269`; (c) `s = 6, 7`: every prime `p ≥ 8.607·10^5`, `5.322·10^7`, and from
`281 053`, `14 642 759` given `Γ < p` at the primes in between (computer-assisted range); (d) every `s ≥ 3`: every prime
`p > max(p_1(s), s)` (mixed-radix rule, `Γ < p`), with `1 - C'_s p^{-1/s}` for every prime `p ≥ max(Q_s^s u^{*s}, s)`
(any real `u^* > u_min` with `F(u^*) < 1`; `thm:MRall`(c)), and every prime `p ≥ p_0(s)` (staggered rule) with
`1 - C''_s/p` (`dim45_q4`, `dim45_primes`). The Lean statement additionally carries the conditional conjunct
`p = 211`, `s = 5` (`2/211`, given the computer-assisted coverings of columns `3`, `4`), which is `rem:p211` — stronger
than the theorem, with the covering hypothesis explicit. -/
theorem dim45 :
    QUSep f4code 4 S4gen (3013 / 100000) ∧
    (∃ C : Gen 4 (ZMod 37), QUSep (zcode 37) 4 C (1 / 37)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 47 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (67 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (163 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 4 (ZMod p), QUSep (zcode p) 4 C (((p : ℝ) - Γ) / p)) ∧
    (edCover 211 edP211 3 = true → edCover 211 edP211 4 = true →
      edValid 211 edP211 ∧ edCost edP211 = 209 ∧ ∃ C : Gen 5 (ZMod 211), QUSep (zcode 211) 5 C (2 / 211)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 269 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (373 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (1277 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 5 (ZMod p), QUSep (zcode p) 5 C (((p : ℝ) - Γ) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 860700 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
      ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 281053 ≤ p → p < 860700 → mrCost 6 p (mrRuleH 6 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 281053 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
        ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 53220000 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
      ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 14642759 ≤ p → p < 53220000 → mrCost 7 p (mrRuleH 7 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 14642759 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
        ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ (p : ℕ) [Fact p.Prime], mrP1 s < p → s < p → mrCost s p (mrRuleH s p) < p ∧
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ us : ℝ, (mrUmin s : ℝ) < us → mrF s us < 1 →
      ∀ (p : ℕ) [Fact p.Prime], (mrQss s : ℝ) * us ^ s ≤ p → s ≤ p → mrCost s p (mrRuleH s p) < p ∧
        1 - mrCp s us * (p : ℝ) ^ (-(1 : ℝ) / s) ≤ ((p : ℝ) - mrCost s p (mrRuleH s p)) / p ∧
        ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∃ (p0 : ℕ) (C'' : ℝ), ∀ (p : ℕ) [Fact p.Prime], p0 ≤ p →
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (1 - C'' / p)) :=
  ⟨dim45_q4, dim45_primes⟩

end GeoSeq
