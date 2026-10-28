/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7P7
public import GeoSeq.V4LF3
public import GeoSeq.V5A3
public import GeoSeq.S3Cert
public import GeoSeq.K4Cert

@[expose] public section

/-!
# GeoSeq stage V7: dimension three (`thm:dim3`, `tab:dim3`)

* Helpers: `qusep_of` (`IsSeq0` + separation `LB > 0` ⇒ `QUSep`, via `prefix_mesh`),
  `qusep_mono`, `lb_pos`.
* **`dim3_primes`**: the rows of `tab:dim3` with prime bases: `p = 7` (graph rule, `thm:p7`, `1/7`), `p = 11`
  (`thm:LF`(b), `1/11`), every prime `p ≥ 13` (`thm:LF`(a): `(p-Γ)/p > 0.1`, `≥ 0.3` from `31`), every prime
  `p ≥ 41` (mixed-radix rule, `thm:MRall`, `tab:P1`: `1 - 3.99 p^{-1/3}` from `67`), every prime `p ≥ 1.97·10^7`
  (staggered rule, `thm:A3`, `1 - 742/p`).
* **`dim3_every_prime`**: every prime `p ≥ 7` has a quasi-uniform digital `(0,3)`-sequence with a positive bound
  (`1/7`, `1/11`, `> 0.1` from `13`).
* **`dim3_of_small`**, **`dim3`** (`thm:dim3`): `q = 3` (`thm:S3`, `0.05598`), `q = 4` (`thm:K4`, `0.11293`) and
  every prime `p ≥ 7`, with the rows of `tab:dim3`. `dim3_of_small` takes the statements of `S3_net`, `S3_sep`,
  `K4_net`, `K4_sep` as hypotheses (they are compared in `comparatorGeoSeqS3.json`, `comparatorGeoSeqK4.json`;
  their kernel replay takes ≈ 14 + ≈ 11 min, so they are not replayed again in the V7 configuration); `dim3` is
  the unconditional theorem (= `dim3_of_small S3_net S3_sep K4_net K4_sep`).
-/

namespace GeoSeq

open Finset

section Helpers

variable {R : Type*} [CommRing R] {q s : ℕ}

/-- `IsSeq0` and `c(P_{sK}) ≥ LB > 0` for every `K ≥ 1` give `QUSep` (`lem:prefix`, `prefix_mesh`). -/
lemma qusep_of [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s) (hseq : IsSeq0 D C)
    (LB : ℝ) (hLB : 0 < LB) (hsep : ∀ K : ℕ, 1 ≤ K → SepAtLevel q s K (seqPoint D C) LB) :
    QUSep D s C LB :=
  ⟨hseq, hsep, fun N hN => prefix_mesh D C hq hs hseq LB hLB hsep N hN⟩

lemma qusep_mono [NeZero q] {D : DigitCode R q} {C : Gen s R} (hq : 2 ≤ q) (hs : 1 ≤ s) {LB LB' : ℝ}
    (h : QUSep D s C LB) (hLB' : 0 < LB') (hle : LB' ≤ LB) : QUSep D s C LB' :=
  qusep_of D C hq hs h.1 LB' hLB' fun K hK => sepAtLevel_mono _ hle (h.2.1 K hK)

lemma lb_pos {p Γ : ℕ} (hΓ : Γ < p) : (0 : ℝ) < ((p : ℝ) - Γ) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have : (Γ : ℝ) < p := by exact_mod_cast hΓ
  exact div_pos (by linarith) hp

end Helpers

/-- **`tab:dim3`, the prime bases**: `p = 7` (graph rule, `thm:p7`: `1/7`); `p = 11` (`thm:LF`(b): `1/11`); every prime
`p ≥ 13` (archived ordered designs or the mixed-radix rule, `thm:LF`(a): `(p - Γ)/p > 0.1`, and `≥ 0.3` from `31`);
every prime `p ≥ 41` (mixed-radix rule, `thm:MRall`, `tab:P1`: `Γ < p`, and `(p-Γ)/p ≥ 1 - 3.99 p^{-1/3}` from
`67`); every prime `p ≥ 1.97·10^7` (staggered rule, `thm:A3`: `1 - 742/p`). Each: a quasi-uniform digital
`(0,3)`-sequence over `𝔽_p` with the bound on `c(P_{3K})` for every `K ≥ 1`. -/
theorem dim3_primes :
    (∃ C : Gen 3 (ZMod 7), QUSep (zcode 7) 3 C (1 / 7)) ∧
    (∃ C : Gen 3 (ZMod 11), QUSep (zcode 11) 3 C (1 / 11)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 13 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p ∧
      (31 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - Γ) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 41 ≤ p → mrCost 3 p (mrRuleH 3 p) < p ∧
      (67 ≤ p → 1 - 399 / 100 * (p : ℝ) ^ (-(1 : ℝ) / 3) ≤ ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 19700000 ≤ p → ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (1 - 742 / p)) := by
  refine ⟨p7_exists, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, C, hseq, hsep, -⟩ := LF_b11
    exact ⟨C, qusep_of (zcode 11) C (by norm_num) (by norm_num) hseq _ (by norm_num) hsep⟩
  · intro p hp h13
    obtain ⟨Γ, hΓ, h1, h3, -, C, hseq, hsep, -⟩ := LF_a_s3 p h13
    exact ⟨Γ, hΓ, h1, h3, C, qusep_of (zcode p) C (by omega) (by norm_num) hseq _ (lb_pos hΓ) hsep⟩
  · intro p hp h41
    have hΓ := MR_every_prime_s3 p hp.out h41
    refine ⟨hΓ, fun h67 => ?_, ?_⟩
    · have := (tabP1_s3.2.2.2.2.2.2 p hp.out (by
        have : (67 : ℝ) ≤ p := by exact_mod_cast h67
        push_cast; linarith)).2
      push_cast at this ⊢
      linarith
    · obtain ⟨C, hseq, hsep, -⟩ := mr_rule_seq 3 p le_rfl (by omega) hΓ
      exact ⟨C, qusep_of (zcode p) C (by omega) (by norm_num) hseq _ (lb_pos hΓ) hsep⟩
  · intro p hp hbig
    obtain ⟨⟨zθ, hroot, hplace⟩, hall⟩ := A3 hbig
    obtain ⟨⟨rule, hrule⟩, hrules, -⟩ := hall zθ hroot hplace
    obtain ⟨hseq, hsep, -⟩ := hrules rule hrule
    have hpos : (0 : ℝ) < 1 - 742 / p := by
      have : (19700000 : ℝ) ≤ p := by exact_mod_cast hbig
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    exact ⟨_, qusep_of (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep⟩

/-- **`thm:dim3`, the primes**: every prime `p ≥ 7` has a quasi-uniform digital `(0,3)`-sequence over `𝔽_p` with a
positive lower bound `LB` on `c(P_{3K})` for every `K ≥ 1`: `LB = 1/7` at `p = 7`, `1/11` at `p = 11`, `LB > 0.1`
from `13` on (`tab:dim3`). -/
theorem dim3_every_prime (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) :
    ∃ LB : ℝ, 0 < LB ∧ (p = 7 → LB = 1 / 7) ∧ (p = 11 → LB = 1 / 11) ∧ (13 ≤ p → 1 / 10 < LB) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C LB := by
  obtain ⟨h7', h11', h13', -, -⟩ := dim3_primes
  by_cases hp13 : 13 ≤ p
  · obtain ⟨Γ, hΓ, h1, -, C, hC⟩ := h13' p hp13
    exact ⟨_, lb_pos hΓ, fun h => by omega, fun h => by omega, fun _ => h1, C, hC⟩
  · have hcases : p = 7 ∨ p = 11 := by
      have hpr := hp.out
      interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hpr; decide)
    rcases hcases with rfl | rfl
    · exact ⟨1 / 7, by norm_num, fun _ => rfl, fun h => by omega, fun h => by omega, h7'⟩
    · exact ⟨1 / 11, by norm_num, fun h => by omega, fun _ => rfl, fun h => by omega, h11'⟩

lemma s3_lb : (5598 / 100000 : ℝ) ≤ Real.sqrt 134917 / 6561 := by
  rw [le_div_iff₀ (by norm_num)]
  exact Real.le_sqrt_of_sq_le (by norm_num)

lemma k4_lb : (11293 / 100000 : ℝ) ≤ Real.sqrt 54774953 / 65536 := by
  rw [le_div_iff₀ (by norm_num)]
  exact Real.le_sqrt_of_sq_le (by norm_num)

/-- **`thm:dim3` from the small-base theorems** (`tab:dim3`): given the statements of `thm:S3` (`S3_net`, `S3_sep`)
and `thm:K4` (`K4_net`, `K4_sep`): for `q = 3` (the sequence `S3gen` of `thm:S3`, `c(P_{3K}) ≥ 0.05598`), `q = 4`
(the sequence `K4gen` of `thm:K4`, `≥ 0.11293`) and every prime
`p ≥ 7` there is a quasi-uniform digital `(0,3)`-sequence over `𝔽_q` with an explicit positive lower bound on
`c(P_{3K})` for every `K ≥ 1`, with the rows of `tab:dim3` (`dim3_primes`). -/
theorem dim3_of_small (hS3n : IsSeq0 (zcode 3) S3gen)
    (hS3s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 3 3 K (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561))
    (hK4n : IsSeq0 f4code K4gen)
    (hK4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 3 K (seqPoint f4code K4gen) (Real.sqrt 54774953 / 65536)) :
    QUSep (zcode 3) 3 S3gen (5598 / 100000) ∧ QUSep f4code 3 K4gen (11293 / 100000) ∧
    (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ LB : ℝ, 0 < LB ∧ (p = 7 → LB = 1 / 7) ∧ (p = 11 → LB = 1 / 11) ∧
      (13 ≤ p → 1 / 10 < LB) ∧ ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C LB) ∧
    (∀ (p : ℕ) [Fact p.Prime], 41 ≤ p → mrCost 3 p (mrRuleH 3 p) < p ∧
      (67 ≤ p → 1 - 399 / 100 * (p : ℝ) ^ (-(1 : ℝ) / 3) ≤ ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 19700000 ≤ p → ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (1 - 742 / p)) := by
  obtain ⟨-, -, -, hMR, hA3⟩ := dim3_primes
  refine ⟨qusep_of (zcode 3) S3gen (by norm_num) (by norm_num) hS3n _ (by norm_num)
      fun K hK => sepAtLevel_mono _ s3_lb (hS3s K hK),
    qusep_of f4code K4gen (by norm_num) (by norm_num) hK4n _ (by norm_num)
      fun K hK => sepAtLevel_mono _ k4_lb (hK4s K hK),
    fun p _ h7 => dim3_every_prime p h7, hMR, hA3⟩

/-- **`thm:dim3`** (dimension three; `tab:dim3`): for `q = 3`, `q = 4` and every prime `p ≥ 7` there is a quasi-uniform
digital `(0,3)`-sequence over `𝔽_q` with an explicit positive lower bound on `c(P_{3K})` for every `K ≥ 1`:
`0.05598` (`q = 3`, the Artin–Schreier sequence `S3gen` of `thm:S3`), `0.11293` (`q = 4`, the Kummer sequence `K4gen`
over `𝔽_4` of `thm:K4`),
`1/7` (`p = 7`, graph rule, `thm:p7`), `1/11` (`p = 11`, `thm:LF`(b)), `(p-Γ)/p > 0.1` (every prime `p ≥ 13`,
`thm:LF`(a)); and the further rows: mixed-radix rule from `41` (`1 - 3.99 p^{-1/3}` from `67`), staggered rule from
`1.97·10^7` (`1 - 742/p`). -/
theorem dim3 :
    QUSep (zcode 3) 3 S3gen (5598 / 100000) ∧ QUSep f4code 3 K4gen (11293 / 100000) ∧
    (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ LB : ℝ, 0 < LB ∧ (p = 7 → LB = 1 / 7) ∧ (p = 11 → LB = 1 / 11) ∧
      (13 ≤ p → 1 / 10 < LB) ∧ ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C LB) ∧
    (∀ (p : ℕ) [Fact p.Prime], 41 ≤ p → mrCost 3 p (mrRuleH 3 p) < p ∧
      (67 ≤ p → 1 - 399 / 100 * (p : ℝ) ^ (-(1 : ℝ) / 3) ≤ ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 19700000 ≤ p → ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (1 - 742 / p)) :=
  dim3_of_small S3_net S3_sep K4_net K4_sep

end GeoSeq
