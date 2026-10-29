/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V99Defs

@[expose] public section

/-!
# GeoSeq stage V10-1: definitions for the sign-class argument (`GeoSeq/V10_1Sign.lean`)

* `stepSig Mz e l i = ∑_c e_c M^{(min(l_c, s-1) - 1)}[i][c]`, the change of the geometric digit `i` for the step
  `(e, l)` (`thm:block`(iii); the same body as `caSig` of `GeoSeq/V99Gen.lean`).
* `SignClass Mz A`: every step has a backward coordinate (`e_i ≠ 0`, `e_i σ_i ≤ 0`) with `|σ_i| ≤ A`, or at least two
  backward coordinates — a `p`-independent condition that replaces diagonal dominance.
-/

namespace GeoSeq

variable {s : ℕ}

/-- The change `σ_i = ∑_c e_c M^{(min(l_c, s-1) - 1)}[i][c]` of the geometric digit `i` for the step `(e, l)`. -/
def stepSig (Mz : ℕ → Fin s → Fin s → ℤ) (e : Fin s → ℤ) (l : Fin s → ℕ) (i : Fin s) : ℤ :=
  ∑ c, e c * Mz (min (l c) (s - 1) - 1) i c

/-- The finitely checkable condition (independent of `p`): every step has a backward coordinate with `|σ_i| ≤ A`, or
two backward coordinates. -/
def SignClass (Mz : ℕ → Fin s → Fin s → ℤ) (A : ℕ) : Prop :=
  ∀ K e l, IsStep K e l →
    (∃ i, e i ≠ 0 ∧ e i * stepSig Mz e l i ≤ 0 ∧ |stepSig Mz e l i| ≤ A) ∨
    (∃ i i', i ≠ i' ∧ e i ≠ 0 ∧ e i * stepSig Mz e l i ≤ 0 ∧ e i' ≠ 0 ∧ e i' * stepSig Mz e l i' ≤ 0)

end GeoSeq
