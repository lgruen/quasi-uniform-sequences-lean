/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# Statements: the level law and the certificate (`sec:law`), GeoSeq stage S0

Compared theorems (statement with `sorry`; proofs in `GeoSeq/OneDigit.lean`, restated by name).

* `rem:onedigit`: the closed form of the one-digit gap `f_1` over `ℤ/qℤ` (`gapNum1_zero`,
  `gapNum1_eq`), `f_1(1, -A) = 1 - (A+1)/q` (`F1_one_neg`), `f_1(1, 1) = 0` (`F1_one_one`),
  `f_1(-1, σ) = f_1(1, -σ)` (`F1_neg`), `f_1(0, ±1/2) = (p-3)/(2p)` (`F1_zero_half`), and the
  depth-one case of the general `f_j` (`gapNum_one`).
-/

namespace GeoSeq

/-- **`rem:onedigit`**: `f_1(e, 0)` has numerator `|e q| - 1`. -/
theorem gapNum1_zero (q : ℕ) [NeZero q] (e : ℤ) : gapNum1 q e 0 = (e * q).natAbs - 1 := by
  sorry

/-- **`rem:onedigit`**: for `σ ≠ 0`, `f_1(e, σ)` has numerator
`min(|e q + val σ|, |e q + val σ - q|) - 1`. -/
theorem gapNum1_eq (q : ℕ) [NeZero q] (e : ℤ) (σ : ZMod q) (hσ : σ ≠ 0) :
    gapNum1 q e σ =
      min (e * q + σ.val).natAbs (e * q + σ.val - q).natAbs - 1 := by
  sorry

/-- **`rem:onedigit`**: `f_1(1, -A) = 1 - (A+1)/q` for `0 ≤ A < q` (numerators). -/
theorem F1_one_neg (q : ℕ) [NeZero q] (A : ℕ) (hA : A < q) :
    gapNum1 q 1 (-(A : ZMod q)) = q - 1 - A := by
  sorry

/-- **`rem:onedigit`**: the fatal forward shift, `f_1(1, 1) = 0` (`q ≥ 2`). -/
theorem F1_one_one (q : ℕ) [NeZero q] (hq : 2 ≤ q) : gapNum1 q 1 1 = 0 := by
  sorry

/-- **`rem:onedigit`**: `f_1(-1, σ) = f_1(1, -σ)`. -/
theorem F1_neg (q : ℕ) [NeZero q] (σ : ZMod q) : gapNum1 q (-1) σ = gapNum1 q 1 (-σ) := by
  sorry

/-- **`rem:onedigit`** (the antipode): `f_1(0, ±1/2) = (p-3)/(2p)` for an odd prime `p`. -/
theorem F1_zero_half (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (σ : ZMod p)
    (hσ : σ = (2 : ZMod p)⁻¹ ∨ σ = -(2 : ZMod p)⁻¹) :
    2 * gapNum1 p 0 σ = p - 3 := by
  sorry

/-- At depth `j = 1` the general certificate numerator `gapNum` over `ℤ/qℤ` is `gapNum1`. -/
theorem gapNum_one (q : ℕ) [NeZero q] (e : ℤ) (σ : Fin 1 → ZMod q) :
    gapNum (zcode q) 1 e σ = gapNum1 q e (σ 0) := by
  sorry

end GeoSeq
