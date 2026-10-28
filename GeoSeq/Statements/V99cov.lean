/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99CovDefs

@[expose] public section

/-!
# Statements: stage V99cov (paper V4)

`thm:coverage`(a)–(e) as an assembly theorem (prime-power rows omitted: `prop:primepower` not formalized), with `thm:coverage`(a) for every prime.
PROVED (`GeoSeq/V99Cov.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V99cov`
(definitions in `GeoSeq/V99CovDefs.lean`). Paper: V4 (`paper/sections/10-frames.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV99cov.json`.
-/

namespace GeoSeq

section G0
open Finset
variable {p : ℕ}

/-- **`thm:coverage`(a)**: for every prime `p` there is a digital `(0,2)`-sequence over `𝔽_p` that is `Covered` on
`2ℕ`: `p = 2` (`thm:B2`), `p = 3` (`rem:B3`), `p ≥ 5` (the brick wall, `thm:WF`). -/
theorem cov_s2 [Fact p.Prime] : ∃ C : Gen 2 (ZMod p), Covered (zcode p) 2 C (levFull 2) := by
  sorry

end G0

section G1
open Finset

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
  sorry

end G1

end GeoSeq
