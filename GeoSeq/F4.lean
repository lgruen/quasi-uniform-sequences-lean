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
# GeoSeq stage S8: the field `𝔽_4` with the binary digit code (`sec:prelim`, `rem:F4carry`)

`𝔽_4 = {0, 1, ω, ω²}` as an explicit four-element type with the operations given by tables, and the
field axioms checked by `decide` (finite case checks). We use this rather than `GaloisField 2 2`:
the Galois field is defined as a splitting field, its elements cannot be evaluated by the kernel, and
the automaton certificates of `thm:K4` and `thm:S4` need kernel evaluation of `𝔽_4`-arithmetic. Any
two fields with four elements are isomorphic, so nothing is lost.

The digit code is the paper's (`sec:prelim`): `0, 1, ω, ω² ↦ 0, 1, 2, 3`. Writing `a + bω`
(`a, b ∈ 𝔽_2`; `ω² = 1 + ω`), the code is `a + 2b`, so addition in `𝔽_4` is XOR of the codes.
-/

namespace GeoSeq

/-- The four elements `0, 1, ω, ω² = 1 + ω` of `𝔽_4`. -/
inductive F4 : Type
  | e0 | e1 | ew | ew2
  deriving DecidableEq, Repr

namespace F4

instance : Fintype F4 := ⟨⟨{e0, e1, ew, ew2}, by decide⟩, fun x => by cases x <;> decide⟩

/-- Addition (XOR of the binary codes). -/
def add : F4 → F4 → F4
  | e0, x => x
  | x, e0 => x
  | e1, e1 => e0
  | e1, ew => ew2
  | e1, ew2 => ew
  | ew, e1 => ew2
  | ew, ew => e0
  | ew, ew2 => e1
  | ew2, e1 => ew
  | ew2, ew => e1
  | ew2, ew2 => e0

/-- Multiplication (`ω³ = 1`). -/
def mul : F4 → F4 → F4
  | e0, _ => e0
  | _, e0 => e0
  | e1, x => x
  | x, e1 => x
  | ew, ew => ew2
  | ew, ew2 => e1
  | ew2, ew => e1
  | ew2, ew2 => ew

/-- Inverse (`0⁻¹ = 0`). -/
def inv : F4 → F4
  | e0 => e0
  | e1 => e1
  | ew => ew2
  | ew2 => ew

instance : Zero F4 := ⟨e0⟩
instance : One F4 := ⟨e1⟩
instance : Add F4 := ⟨add⟩
instance : Mul F4 := ⟨mul⟩
instance : Neg F4 := ⟨id⟩
instance : Sub F4 := ⟨add⟩
instance : Inv F4 := ⟨inv⟩

lemma add_def (a b : F4) : a + b = add a b := rfl
lemma mul_def (a b : F4) : a * b = mul a b := rfl

instance : CommRing F4 where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  sub_eq_add_neg a b := by cases a <;> cases b <;> rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Field F4 where
  mul_inv_cancel a h := by cases a <;> first | rfl | exact absurd rfl h
  inv_zero := rfl
  exists_pair_ne := ⟨e0, e1, by decide⟩
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- `ω`. -/
abbrev w : F4 := ew
/-- `ω² = 1 + ω`. -/
abbrev w2 : F4 := ew2

end F4

/-- The binary digit code of `𝔽_4` (`sec:prelim`): `0, 1, ω, ω² ↦ 0, 1, 2, 3`. -/
def f4enc : F4 → Fin 4
  | .e0 => 0
  | .e1 => 1
  | .ew => 2
  | .ew2 => 3

/-- The inverse of the code. -/
def f4dec : Fin 4 → F4 := ![.e0, .e1, .ew, .ew2]

/-- **The digit code of `𝔽_4`** (`sec:prelim`). -/
def f4code : DigitCode F4 4 where
  enc :=
    { toFun := f4enc
      invFun := f4dec
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  enc_zero := rfl

/-- `ω^n` (`n mod 3`), the powers of the generator of `𝔽_4^*`. -/
def wpn (n : ℕ) : F4 := if n % 3 = 0 then 1 else if n % 3 = 1 then F4.w else F4.w2

/-- `m(d)`: the least change of a digit with code `d ≠ 0` (`1, 2, 1` for `d = 1, 2, 3`). -/
def mdig (d : ℕ) : ℕ := if d = 2 then 2 else 1

/-- `topF4` computed on the word `enc σ`: for `w < 4^j`, the leading nonzero base-4 digit `d` of `w`
(at position `k`) gives `m(d) 4^k − (w mod 4^k)`; `0` for `w = 0`. -/
def topW : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, w => if w / 4 ^ j = 0 then topW j w else mdig (w / 4 ^ j) * 4 ^ j - w % 4 ^ j

end GeoSeq
