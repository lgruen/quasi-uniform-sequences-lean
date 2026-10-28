/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S4Defs

@[expose] public section

/-!
# GeoSeq stage S8: definitions for the translation symmetry of `thm:S4`

The places `a_c` of `thm:S4` are the elements of `𝔽_4` in the order of their codes, so the translation
`z ↦ z + a_h` permutes the coordinates by `c ↦ c ⊕ h` (XOR of the codes, `fxor`); `S4P h` is the constant
matrix of the substitution `(z + a_h)^b = ∑_{b'} P_h[b'][b] z^{b'}` (`GeoSeq/S4Law.lean`, `S4_rot`).
-/

namespace GeoSeq

/-- Addition of places: `a_{c ⊕ h} = a_c + a_h` (XOR of the codes). -/
def fxor (a b : Fin 4) : Fin 4 := ⟨(a : ℕ) ^^^ (b : ℕ), Nat.xor_lt_two_pow (n := 2) a.isLt b.isLt⟩

/-- The matrix `P_h[b'][b] = C(b, b') a_h^{b-b'}` (mod `2`) of the translation `z ↦ z + a_h`. -/
def S4P (h b' b : Fin 4) : F4 := if (b' : ℕ) ≤ b ∧ Nat.choose b b' % 2 = 1 then S4a h ^ ((b : ℕ) - b') else 0

end GeoSeq
