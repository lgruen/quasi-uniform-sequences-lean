/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs
public import GeoSeq.S3Defs
public import GeoSeq.S4Defs
public import GeoSeq.V94Defs
public import GeoSeq.V99Defs

@[expose] public section

/-!
# GeoSeq stage V9-9: definitions for `thm:coverage`

* Level families: `levFull s = sℕ` (the full levels `m = sK`, `K ≥ 1`), `levPre s = sℕ - 1`, `levSq s = s²ℕ`.
* `Covered D s C Lev`: `C` is a digital `(0,s)`-sequence (digit code `D`), there is `LB > 0` with `sep(P_m) ≥ LB`
  (toroidal, normalized: `SepAtPrefix`) for every `m` of the level family, and it is quasi-uniform (`IsQuasiUniform`,
  bounded Euclidean mesh ratio over all `N ≥ 2`) — the conclusion of `thm:coverage` in each case.
-/

namespace GeoSeq

/-- The full levels `sℕ = {sK : K ≥ 1}`. -/
def levFull (s : ℕ) : ℕ → Prop := fun m => ∃ K, 1 ≤ K ∧ m = s * K

/-- The prefixes `sℕ - 1 = {sK - 1 : K ≥ 1}`. -/
def levPre (s : ℕ) : ℕ → Prop := fun m => ∃ K, 1 ≤ K ∧ m = s * K - 1

/-- Every `s`-th full level, `s²ℕ = {s²K : K ≥ 1}`. -/
def levSq (s : ℕ) : ℕ → Prop := fun m => ∃ K, 1 ≤ K ∧ m = s ^ 2 * K

/-- **The conclusion of `thm:coverage`** for one sequence and one level family: a digital `(0,s)`-sequence with a
positive lower bound on `sep(P_m)` for every `m` in `Lev`, and quasi-uniform. -/
def Covered {R : Type*} [CommRing R] {q : ℕ} [NeZero q] (D : DigitCode R q) (s : ℕ) (C : Gen s R)
    (Lev : ℕ → Prop) : Prop :=
  IsSeq0 D C ∧ (∃ LB : ℝ, 0 < LB ∧ ∀ m, Lev m → SepAtPrefix q s m (seqPoint D C) LB) ∧
    IsQuasiUniform (seqPoint D C)

end GeoSeq

namespace GeoSeq

/-- The primes `19 ≤ p ≤ 83` of the computer-assisted range of `thm:block`(c), `s = 5`, below its proof range. -/
def blk5CAPrimes : List ℕ := [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]

/-- The kernel evaluations of `thm:block`(c), `s = 5`, at the primes `19 ≤ p ≤ 83` (`caCheck`; proved one prime at a
time by `decide +kernel` in `GeoSeq/V99Ca5a.lean`–`V99Ca5d.lean`, theorems `blk5_chk19` … `blk5_chk83`). -/
def Blk5CA : Prop := ∀ q ∈ blk5CAPrimes, caCheck 5 blk5Opts blk5St0 q 16 = true

end GeoSeq
