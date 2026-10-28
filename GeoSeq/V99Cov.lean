/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99CovDefs
public import GeoSeq.V9QU
public import GeoSeq.V9Kor
public import GeoSeq.V94Dyadic
public import GeoSeq.V94WF
public import GeoSeq.V96Two
public import GeoSeq.V96Inst
public import GeoSeq.V99Blk4
public import GeoSeq.V99Blk5Main
public import GeoSeq.V99Blk5Cond
public import GeoSeq.B2Cert
public import GeoSeq.B3Cert
public import GeoSeq.S3Cert
public import GeoSeq.K4Cert
public import GeoSeq.S4Cert
public import GeoSeq.V7P7

@[expose] public section

/-!
# GeoSeq stage V9-9: `thm:coverage` as an assembly theorem

* `prefix_of_level` (`sep(P_{sK})` in the two normalizations), `hasGap_sN`; **`covered_of_level`**: a `(0,s)`-sequence
  with `sep(P_m) ≥ LB > 0` on a level family of bounded gap is `Covered` (`lem:prefix`).
* The cases: `cov_dyadic` and `cov_residue` (`thm:coverage`(e)), `cov_s2` ((a), every prime), the small bases, the
  block-periodic families `s²ℕ` (`thm:block`(a)–(c)), and **`coverage`** (`thm:coverage`(a)–(e)) WITHOUT the
  prime-power rows (those need `prop:primepower`, whose computer-assisted values `β_q(k)` are not formalized).
-/

namespace GeoSeq

open Finset

section Cov

/-- `sep(P_{sK}) ≥ LB` in the level normalization (`SepAtLevel`, distances times `q^K`) gives the prefix
normalization (`SepAtPrefix`, distances times `N^{1/s}`, `N = q^{sK}`). -/
lemma prefix_of_level {q s K : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ) (LB : ℝ)
    (h : SepAtLevel q s K pt LB) : SepAtPrefix q s (s * K) pt LB := by
  intro v w hv hw hvw
  have h1 := h v w hv hw hvw
  have hqK : (0 : ℝ) < (q : ℝ) ^ K := by positivity
  have e : ((q : ℝ) ^ (s * K)) ^ (-(1 / (s : ℝ))) = ((q : ℝ) ^ K)⁻¹ := by
    rw [mul_comm, pow_mul, Real.rpow_neg (by positivity), one_div,
      Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  rw [e, ← div_eq_mul_inv, div_le_iff₀ hqK, mul_comm]
  exact h1

lemma hasGap_sN {s : ℕ} (hs : 1 ≤ s) : HasGap (levFull s) s := by
  intro m
  refine ⟨s * (m / s + 1), ⟨m / s + 1, Nat.le_add_left 1 _, rfl⟩, ?_, ?_⟩
  · have := Nat.lt_mul_div_succ m (show 0 < s by omega); linarith
  · have := Nat.mul_div_le m s; rw [Nat.mul_succ]; linarith

/-- **`lem:prefix` for `thm:coverage`**: a digital `(0,s)`-sequence with `sep(P_m) ≥ LB > 0` for every `m` of a level
family with largest gap `≤ Δ` is `Covered` (in particular quasi-uniform). -/
theorem covered_of_level {R : Type*} [CommRing R] {q s : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q)
    (hs : 1 ≤ s) (C : Gen s R) (hseq : IsSeq0 D C) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ) (LB : ℝ)
    (hLB : 0 < LB) (h : ∀ m, Lev m → SepAtPrefix q s m (seqPoint D C) LB) : Covered D s C Lev := by
  refine ⟨hseq, ⟨LB, hLB, h⟩, qu_of_sepAllN D C hq hs hseq _ ?_ (prefix_sep_gap q s hq _ Lev Δ hgap LB hLB.le h)⟩
  have : (0 : ℝ) < ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ))) :=
    Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast (show 0 < q by omega)) _) _
  positivity

/-- Full-level bounds give `Covered` on `sℕ`. -/
theorem covered_full {R : Type*} [CommRing R] {q s : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q)
    (hs : 1 ≤ s) (C : Gen s R) (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K, 1 ≤ K → SepAtLevel q s K (seqPoint D C) LB) : Covered D s C (levFull s) :=
  covered_of_level D hq hs C hseq _ s (hasGap_sN hs) LB hLB fun m ⟨K, hK, hm⟩ => by
    rw [hm]; exact prefix_of_level (by omega) hs _ LB (h K hK)

/-- Bounds at every `s`-th full level give `Covered` on `s²ℕ`. -/
theorem covered_sq {R : Type*} [CommRing R] {q s : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q)
    (hs : 1 ≤ s) (C : Gen s R) (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K, 1 ≤ K → SepAtLevel q s (s * K) (seqPoint D C) LB) : Covered D s C (levSq s) :=
  covered_of_level D hq hs C hseq _ (s ^ 2) (hasGap_s2N hs) LB hLB fun m ⟨K, hK, hm⟩ => by
    rw [hm, sq, mul_assoc]; exact prefix_of_level (by omega) hs _ LB (h K hK)

variable {p : ℕ}

/-- **`thm:coverage`(e), first sequence**: for every `s ≥ 2` and prime `p > 2^s`, the staggered residue sequence with
dyadic weights (Faure places, `θ = μ⋆ = 1`, `c⋆ = 0`, standard order; `cor:dyadic`) is `Covered` on `sℕ`. -/
theorem cov_dyadic [Fact p.Prime] {s : ℕ} (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    Covered (zcode p) s (resStar (faurePlace p) 1 ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hs⟩ 1
      (dyadicK p (stdOrder ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hs⟩))) (levFull s) := by
  have hsp : s ≤ p := by
    have : s < 2 ^ s := Nat.lt_two_pow_self
    omega
  obtain ⟨hseq, hsep, -⟩ := dyadic_qu hs hps (faurePlace p) (faurePlace_injective hsp) 1 one_ne_zero
    ⟨0, by omega⟩ 1 one_ne_zero (stdOrder ⟨0, by omega⟩)
    (fun c c' hc hc' h => stdOrder_inj _ c c' hc hc' h) (fun c hc => stdOrder_lt _ c hc)
  refine covered_full (zcode p) (Fact.out : p.Prime).two_le (by omega) _ hseq _ ?_ hsep
  have h2 : 2 ≤ p / 2 ^ (s - 1) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have : (2 : ℝ) ≤ ((p / 2 ^ (s - 1) : ℕ) : ℝ) := by exact_mod_cast h2
  exact div_pos (by linarith) (by exact_mod_cast (Fact.out : p.Prime).pos)

/-- **`thm:coverage`(e), second sequence**: for every `s ≥ 2` and prime `p > 2^s`, the residue sequence with the
Korobov check vector (Faure places, `θ = 1`; `cor:korobov`, `cor:residueQU`) is `Covered` on `sℕ - 1`. -/
theorem cov_residue [Fact p.Prime] {s : ℕ} (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    Covered (zcode p) s (resSeq (faurePlace p) 1 (korobov p s)) (levPre s) := by
  obtain ⟨hseq, hsep, hpos, -⟩ := residue_korobov hs hps
  refine covered_of_level (zcode p) (Fact.out : p.Prime).two_le (by omega) _ hseq _ s (hasGap_sN1 hs) _ hpos
    fun m ⟨K, hK, hm⟩ => ?_
  intro v w hv hw hvw
  rw [hm] at hv hw ⊢
  have := hsep K hK v w hv hw hvw
  rwa [Nat.cast_pow, neg_div] at this

/-- **`thm:coverage`(a)**: for every prime `p` there is a digital `(0,2)`-sequence over `𝔽_p` that is `Covered` on
`2ℕ`: `p = 2` (`thm:B2`), `p = 3` (`rem:B3`), `p ≥ 5` (the brick wall, `thm:WF`). -/
theorem cov_s2 [Fact p.Prime] : ∃ C : Gen 2 (ZMod p), Covered (zcode p) 2 C (levFull 2) := by
  have hp2 := (Fact.out : p.Prime).two_le
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      · left; rfl
      · right; left; rfl
      · exact absurd (Fact.out : (4 : ℕ).Prime) (by decide)
    · right; right; exact h) with rfl | rfl | h5
  · exact ⟨B2gen, covered_full (zcode 2) le_rfl (by norm_num) _ B2_net _ (by positivity) B2_sep⟩
  · exact ⟨B3gen, covered_full (zcode 3) (by norm_num) (by norm_num) _ B3_net _ (by positivity) B3_sep⟩
  · obtain ⟨hseq, hsep, -⟩ := brickWall_WF h5
    refine ⟨brickWall p, covered_full (zcode p) hp2 (by norm_num) _ hseq _ ?_ hsep⟩
    have : (5 : ℝ) ≤ p := by exact_mod_cast h5
    exact div_pos (by linarith) (by linarith)

/-- **`thm:coverage`, modular form** (as `dim3_of_small` in V7): the assembly with the statements of the heavy
computer-assisted parts as hypotheses — `thm:S3` (`hS3n`, `hS3s`), `thm:K4` (`hK4n`, `hK4s`), `thm:S4` (`hS4n`, `hS4s`) and
the kernel evaluations of `thm:block`(c), `s = 5` (`hca`). See `coverage` for the unconditional theorem and the case list. In each case there is a digital
`(0,s)`-sequence over `𝔽_q` with a positive lower bound on `sep(P_m)` for every `m` of the stated level family, and it
is quasi-uniform (`Covered`; the sequences are explicit in the proofs of the cited results):
(a) `s = 2`: every prime `p`, `2ℕ` (`thm:B2`, `rem:B3`, `thm:WF`);
(b) `s = 3`: `q = 3` (`thm:S3`), `q = 4` (`thm:K4`), `q = 7` (`thm:p7`) and every prime `p ≥ 11` (case (e)), `3ℕ`; every
prime `p ≥ 5`, `9ℕ` (`thm:block`(b));
(c) `s = 4`: `q = 4` (`thm:S4`) and every prime `p ≥ 17`, `4ℕ`; every prime `p ≥ 7`, `16ℕ` (`thm:block`(c));
(d) `s = 5`: every prime `p ≥ 37`, `5ℕ`; every prime `p ≥ 19`, `25ℕ` (`thm:block`(c));
(e) every `s ≥ 2` and prime `p > 2^s`: `sℕ` (`cor:dyadic`) and, by a second sequence, `sℕ - 1` (`cor:korobov`,
`cor:residueQU`).
The prime powers `q = 8, 9, 16, 25, 27, 49` (`s = 2`) and `25, …, 125` (`s = 3`) of (a), (b) rest on `prop:primepower`
(computer-assisted values `β_q(k)`), which is not formalized; they are not part of this statement. -/
theorem coverage_of_parts (hS3n : IsSeq0 (zcode 3) S3gen)
    (hS3s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 3 3 K (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561))
    (hK4n : IsSeq0 f4code K4gen)
    (hK4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 3 K (seqPoint f4code K4gen) (Real.sqrt 54774953 / 65536))
    (hS4n : IsSeq0 f4code S4gen)
    (hS4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 4 K (seqPoint f4code S4gen) (Real.sqrt 952 / 1024)) (hca : Blk5CA) :
    (∀ (p : ℕ) [Fact p.Prime], ∃ C : Gen 2 (ZMod p), Covered (zcode p) 2 C (levFull 2)) ∧
    (Covered (zcode 3) 3 S3gen (levFull 3) ∧ Covered f4code 3 K4gen (levFull 3) ∧
      (∃ C : Gen 3 (ZMod 7), Covered (zcode 7) 3 C (levFull 3)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 11 ≤ p → ∃ C : Gen 3 (ZMod p), Covered (zcode p) 3 C (levFull 3)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∃ C : Gen 3 (ZMod p), Covered (zcode p) 3 C (levSq 3))) ∧
    (Covered f4code 4 S4gen (levFull 4) ∧
      (∀ (p : ℕ) [Fact p.Prime], 17 ≤ p → ∃ C : Gen 4 (ZMod p), Covered (zcode p) 4 C (levFull 4)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ C : Gen 4 (ZMod p), Covered (zcode p) 4 C (levSq 4))) ∧
    ((∀ (p : ℕ) [Fact p.Prime], 37 ≤ p → ∃ C : Gen 5 (ZMod p), Covered (zcode p) 5 C (levFull 5)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 19 ≤ p → ∃ C : Gen 5 (ZMod p), Covered (zcode p) 5 C (levSq 5))) ∧
    (∀ s : ℕ, 2 ≤ s → ∀ (p : ℕ) [Fact p.Prime], 2 ^ s < p →
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levFull s)) ∧
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levPre s))) := by
  have he : ∀ s : ℕ, 2 ≤ s → ∀ (p : ℕ) [Fact p.Prime], 2 ^ s < p →
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levFull s)) ∧
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levPre s)) :=
    fun s hs p _ hps => ⟨⟨_, cov_dyadic hs hps⟩, ⟨_, cov_residue hs hps⟩⟩
  have hblk : ∀ (p : ℕ) [Fact p.Prime] (s : ℕ) (C : Gen s (ZMod p)) (A : ℕ), 2 ≤ s → A < p →
      IsSeq0 (zcode p) C → (∀ K, 1 ≤ K → SepAtLevel p s (s * K) (seqPoint (zcode p) C) (((p : ℝ) - A) / p)) →
      Covered (zcode p) s C (levSq s) := by
    intro p _ s C A hs hA hseq hsep
    refine covered_sq (zcode p) (Fact.out : p.Prime).two_le (by omega) C hseq _ ?_ hsep
    have : (A : ℝ) < p := by exact_mod_cast hA
    exact div_pos (by linarith) (by exact_mod_cast (Fact.out : p.Prime).pos)
  refine ⟨fun p _ => cov_s2, ⟨?_, ?_, ?_, fun p _ h => (he 3 (by norm_num) p (by norm_num; omega)).1, ?_⟩,
    ⟨?_, fun p _ h => (he 4 (by norm_num) p (by norm_num; omega)).1, ?_⟩,
    ⟨fun p _ h => (he 5 (by norm_num) p (by norm_num; omega)).1, ?_⟩, he⟩
  · exact covered_full (zcode 3) (by norm_num) (by norm_num) _ hS3n _ (by positivity) hS3s
  · exact covered_full f4code (by norm_num) (by norm_num) _ hK4n _ (by positivity) hK4s
  · obtain ⟨C, hseq, hsep, -⟩ := p7_exists
    exact ⟨C, covered_full (zcode 7) (by norm_num) (by norm_num) C hseq _ (by norm_num) hsep⟩
  · intro p _ h
    obtain ⟨h1, -, h3⟩ := blk3_block h (1 : ZMod p) one_ne_zero
    exact ⟨_, hblk p 3 _ 2 (by norm_num) (by omega) h1 (by exact_mod_cast h3)⟩
  · exact covered_full f4code (by norm_num) (by norm_num) _ hS4n _ (by positivity) hS4s
  · intro p _ h
    obtain ⟨h1, -, h3⟩ := blk4_block h (1 : ZMod p) one_ne_zero
    exact ⟨_, hblk p 4 _ 6 (by norm_num) (by omega) h1 (by exact_mod_cast h3)⟩
  · intro p _ h
    obtain ⟨h1, -, h3⟩ := blk5_block_of hca h (1 : ZMod p) one_ne_zero
    exact ⟨_, hblk p 5 _ 17 (by norm_num) (by omega) h1 (by exact_mod_cast h3)⟩


/-- The kernel evaluations of `thm:block`(c), `s = 5` (`decide +kernel`, `GeoSeq/V99Ca5a.lean`–`V99Ca5d.lean`). -/
theorem blk5CA_holds : Blk5CA := by
  intro q hq
  simp only [blk5CAPrimes, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [blk5_chk19, blk5_chk23, blk5_chk29, blk5_chk31, blk5_chk37, blk5_chk41, blk5_chk43, blk5_chk47,
    blk5_chk53, blk5_chk59, blk5_chk61, blk5_chk67, blk5_chk71, blk5_chk73, blk5_chk79, blk5_chk83]

/-- **`thm:coverage`** (coverage by dimension; assembly, prime-power rows omitted). In each case there is a digital
`(0,s)`-sequence over `𝔽_q` with a positive lower bound on `sep(P_m)` for every `m` of the stated level family, and it
is quasi-uniform (`Covered`; the sequences are explicit in the proofs of the cited results):
(a) `s = 2`: every prime `p`, `2ℕ` (`thm:B2`, `rem:B3`, `thm:WF`);
(b) `s = 3`: `q = 3` (`thm:S3`), `q = 4` (`thm:K4`), `q = 7` (`thm:p7`) and every prime `p ≥ 11` (case (e)), `3ℕ`; every
prime `p ≥ 5`, `9ℕ` (`thm:block`(b));
(c) `s = 4`: `q = 4` (`thm:S4`) and every prime `p ≥ 17`, `4ℕ`; every prime `p ≥ 7`, `16ℕ` (`thm:block`(c));
(d) `s = 5`: every prime `p ≥ 37`, `5ℕ`; every prime `p ≥ 19`, `25ℕ` (`thm:block`(c));
(e) every `s ≥ 2` and prime `p > 2^s`: `sℕ` (`cor:dyadic`) and, by a second sequence, `sℕ - 1` (`cor:korobov`,
`cor:residueQU`).
The prime powers `q = 8, 9, 16, 25, 27, 49` (`s = 2`) and `25, …, 125` (`s = 3`) of (a), (b) rest on `prop:primepower`
(computer-assisted values `β_q(k)`), which is not formalized; they are not part of this statement. -/
theorem coverage :
    (∀ (p : ℕ) [Fact p.Prime], ∃ C : Gen 2 (ZMod p), Covered (zcode p) 2 C (levFull 2)) ∧
    (Covered (zcode 3) 3 S3gen (levFull 3) ∧ Covered f4code 3 K4gen (levFull 3) ∧
      (∃ C : Gen 3 (ZMod 7), Covered (zcode 7) 3 C (levFull 3)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 11 ≤ p → ∃ C : Gen 3 (ZMod p), Covered (zcode p) 3 C (levFull 3)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∃ C : Gen 3 (ZMod p), Covered (zcode p) 3 C (levSq 3))) ∧
    (Covered f4code 4 S4gen (levFull 4) ∧
      (∀ (p : ℕ) [Fact p.Prime], 17 ≤ p → ∃ C : Gen 4 (ZMod p), Covered (zcode p) 4 C (levFull 4)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ C : Gen 4 (ZMod p), Covered (zcode p) 4 C (levSq 4))) ∧
    ((∀ (p : ℕ) [Fact p.Prime], 37 ≤ p → ∃ C : Gen 5 (ZMod p), Covered (zcode p) 5 C (levFull 5)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 19 ≤ p → ∃ C : Gen 5 (ZMod p), Covered (zcode p) 5 C (levSq 5))) ∧
    (∀ s : ℕ, 2 ≤ s → ∀ (p : ℕ) [Fact p.Prime], 2 ^ s < p →
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levFull s)) ∧
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levPre s))) :=
  coverage_of_parts S3_net S3_sep K4_net K4_sep S4_net S4_sep blk5CA_holds

end Cov

end GeoSeq
