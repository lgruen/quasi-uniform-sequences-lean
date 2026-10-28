/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Defs

@[expose] public section

/-!
# GeoSeq stage V9-9 (paper V4, `thm:block`(c)): definitions for the block-periodic sequences with `s = 4, 5`

* **Design numerators in factored form** (`ndPoly`): `N_{c,s-1-n} = (z - a_c)^n · N'_{c,n}` with
  `N'_{c,n} = ∑_{k < s-1-n} cf c n k · z^k` (so the vanishing order `n` of `def:block`(a) is visible and the degree is
  `≤ s - 2`); the coefficients are rationals `num / D` with a common denominator `D` (`cfOf`).
* **The instances of `thm:block`(c)** (data of `tab:block`): the design `U*_s` of the nets (`def:Ustar` of the geo
  paper) moved to the places `0, 1, 1/2, …, 1/(s-1)`, row constants `v = (1, 1, 2, …, s-1)`:
  `blk4` (`s = 4`, `a*_4 = 5`, the matrices displayed after the proof of `thm:block`) and `blk5` (`s = 5`, `a*_5 = 16`,
  `U*_5` as produced by the nets' deterministic rule `def:Ustar`). The design numerators (solutions of identity (a)
  of `def:block`) were computed with exact rationals; their denominators are `6` resp. `24`.
* **The computable one-digit relaxation checker** (`caCheck`): an enumeration (`allFold`) of all steps
  `e ∈ {-1,0,1}^s` and capped carry depths `j_c = min(l_c, s-1) - 1` of the moving coordinates; the state is the pair
  `(∑_c code(e_c) 4^c, ∑_i (64 + σ_i) 256^i)` (codes `0, 1, 2` for `e = 0, 1, -1`; the changes `σ_i` packed in base
  `256` with offset `64`), updated by adding the precomputed option `(code · 4^c, e_c · ∑_i M^{(j)}[i][c] 256^i)`;
  each leaf compares `∑_i f_1(e_i, σ_i)²` (numerators, `caGap`) with `(p - A - 1)²`. Evaluated by kernel reduction
  (`decide +kernel`), no `native_decide`.
-/

namespace GeoSeq

open Finset Polynomial

section Nd
variable {F : Type*} [Field F] {s : ℕ}

/-- Rational coefficients `num c n k / D` from a nested list of integer numerators. -/
def cfOf (L : List (List (List ℤ))) (D : ℕ) : Fin s → ℕ → ℕ → F :=
  fun c n k => (((L.getD c []).getD n []).getD k 0 : F) / (D : F)

/-- **Design numerators in factored form**: `Nd c j = (z - a_c)^{s-1-j} ∑_{k < j} cf c (s-1-j) k z^k`, so that
`Nd c (s-1-n) = (z - a_c)^n N'_{c,n}` with `deg N'_{c,n} < s - 1 - n` (`def:block`(a), orders of vanishing). -/
noncomputable def ndPoly (a : Fin s → F) (cf : Fin s → ℕ → ℕ → F) (c : Fin s) (j : ℕ) : F[X] :=
  (X - C (a c)) ^ (s - 1 - j) * ∑ k ∈ range j, C (cf c (s - 1 - j) k) * X ^ k

end Nd

/-! ## The computable checker of the one-digit relaxation -/

/-- Enumeration: `allFold f leaf [o_1, …, o_n] st` is `true` iff `leaf (f (… (f st x_1) …) x_n)` for all `x_k ∈ o_k`. -/
def allFold {σ β : Type} (f : σ → β → σ) (leaf : σ → Bool) : List (List β) → σ → Bool
  | [], st => leaf st
  | o :: L, st => o.all fun x => allFold f leaf L (f st x)

/-- The numerator `f_1(e, σ) · p` of one coordinate, from the code of `e` (`0, 1, 2` for `e = 0, 1, -1`) and the packed
digit `d = 64 + σ`: with `r = σ mod p`, it is `min(r, p - r) - 1` (`r ≠ 0`) resp. `0` for `e = 0`, `r - 1` resp. `p - 1`
for `e = 1`, and `p - 1 - r` for `e = -1`. -/
def caGap (p code d : ℕ) : ℕ :=
  if code = 0 then (if (d + (p - 1) * 64) % p = 0 then 0 else
      min ((d + (p - 1) * 64) % p) (p - (d + (p - 1) * 64) % p) - 1)
  else if code = 1 then (if (d + (p - 1) * 64) % p = 0 then p - 1 else (d + (p - 1) * 64) % p - 1)
  else p - 1 - (d + (p - 1) * 64) % p

/-- `∑_{i < k} caGap(code_i, d_i)²` for the base-`4` codes `eS` and the base-`256` digits `sP`. -/
def caLeafSum (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, eS, sP => caGap p (eS % 4) (sP % 256) ^ 2 + caLeafSum p k (eS / 4) (sP / 256)

/-- The leaf test: the zero step is skipped; otherwise `(p - A - 1)² ≤ ∑_i f_1(e_i, σ_i)² p²`. -/
def caLeaf (s p A : ℕ) (st : ℤ × ℤ) : Bool :=
  st.1 == 0 || Nat.ble ((p - A - 1) ^ 2) (caLeafSum p s st.1.toNat st.2.toNat)

/-- The packed column `∑_i M[i][c] 256^i` of an integer matrix. -/
def caCol {s : ℕ} (M : Fin s → Fin s → ℤ) (c : Fin s) : ℤ := ∑ i : Fin s, M i c * 256 ^ (i : ℕ)

/-- The options of coordinate `c`: no move, or `e = ±1` with carry depth `j < s - 1` (`M^{(j)}` = `Mz j`). -/
def caOpts {s : ℕ} (Mz : ℕ → Fin s → Fin s → ℤ) (c : Fin s) : List (ℤ × ℤ) :=
  (0, 0) :: ((List.range (s - 1)).map fun j => ((4 : ℤ) ^ (c : ℕ), caCol (Mz j) c)) ++
    ((List.range (s - 1)).map fun j => (2 * (4 : ℤ) ^ (c : ℕ), -caCol (Mz j) c))

/-- The initial packed state `∑_i 64 · 256^i`. -/
def caStart (s : ℕ) : ℤ := ∑ i : Fin s, 64 * 256 ^ (i : ℕ)

/-- **The checker**: all steps and capped carry depths, with the options `opts` (literal data equal to
`List.ofFn (fun k => caOpts Mz (Fin.rev k))`) and the start `st0 = caStart s`. -/
def caCheck (s : ℕ) (opts : List (List (ℤ × ℤ))) (st0 : ℤ) (p A : ℕ) : Bool :=
  allFold (· + ·) (caLeaf s p A) opts (0, st0)

/-! ## The instances of `thm:block`(c) -/

section Inst
variable {p : ℕ} [Fact p.Prime]

/-- The places `(0, 1, 1/2, 1/3)` of `thm:block`(c), `s = 4` (`tab:block`). -/
def blk4a : Fin 4 → ZMod p := ![0, 1, (2 : ZMod p)⁻¹, (3 : ZMod p)⁻¹]

/-- The row constants `v = (1, 1, 2, 3)` of `thm:block`(c), `s = 4`. -/
def blk4v : Fin 4 → ZMod p := ![1, 1, 2, 3]

/-- The design `U*_4` of `thm:block`(c) (`F_0, …, F_2`; largest diagonal entry `a*_4 = 5`), in the order of the
places. -/
def blk4F : ℕ → Fin 4 → Fin 4 → ℤ := fun n =>
  if n = 0 then !![-5, 2, 1, 2; 1, -3, -1, -1; 1, 2, -5, -2; 1, 1, 1, -3]
  else if n = 1 then !![0, -3, -1, -1; -2, 0, 2, 1; -1, -1, 0, 3; 0, -1, 0, 0]
  else !![0, 2, 0, -1; 2, 0, -2, 0; 0, -1, 0, -2; -1, 0, -1, 0]

/-- The partial sums `M^{(j)} = F_0 + ⋯ + F_j` of `U*_4` (checked against `blk4F` in the proof modules). -/
def blk4M : ℕ → Fin 4 → Fin 4 → ℤ := fun n =>
  if n = 0 then !![-5, 2, 1, 2; 1, -3, -1, -1; 1, 2, -5, -2; 1, 1, 1, -3]
  else if n = 1 then !![-5, -1, 0, 1; -1, -3, 1, 0; 0, 1, -5, 1; 1, 0, 1, -3]
  else !![-5, 1, 0, 0; 1, -3, -1, 0; 0, 0, -5, -1; 0, 0, 0, -3]

/-- Numerators (over `6`) of the coefficients of `N'_{c,n}` (`c` outer, `n` middle, power `k` inner). -/
def blk4cfL : List (List (List ℤ)) :=
  [[[-1, 3, -4], [-1, -1], [-2]],
    [[-1, 2, -2], [1, 0], [-1]],
    [[4, -14, 14], [-12, 20], [16]],
    [[-6, 30, -39], [18, -45], [-27]]]

/-- The design numerators of `thm:block`(c), `s = 4`: the solutions of identity (a) of `def:block`, in the factored
form `N_{c,4-1-n} = (z - a_c)^n N'_{c,n}`. -/
noncomputable def blk4N : Fin 4 → ℕ → (ZMod p)[X] := ndPoly blk4a (cfOf blk4cfL 6)

/-- **`thm:block`(c), `s = 4`**: the block-periodic residue sequence with `ℓ = s = 4`, places `(0, 1, 1/2, 1/3)`,
`v = (1, 1, 2, 3)` and the design `U*_4`. -/
noncomputable def blk4 (θ : ZMod p) : Gen 4 (ZMod p) :=
  blockGen blk4a θ 4 blk4v (blockF blk4F) blk4N 1

/-- The options of the checker for `s = 4` (literal; equal to `List.ofFn fun k => caOpts blk4M (Fin.rev k)`). -/
def blk4Opts : List (List (ℤ × ℤ)) :=
  [[(0, 0), (64, -50462974), (64, -50266111), (64, -50397184), (128, 50462974), (128, 50266111), (128, 50397184)],
   [(0, 0), (16, 16449281), (16, 16449792), (16, -327936), (32, -16449281), (32, -16449792), (32, 327936)],
   [(0, 0), (4, 16907522), (4, 64767), (4, -767), (8, -16907522), (8, -64767), (8, 767)],
   [(0, 0), (1, 16843003), (1, 16776955), (1, 251), (2, -16843003), (2, -16776955), (2, -251)]]

/-- The start `caStart 4` of the checker (literal). -/
def blk4St0 : ℤ := 1077952576

/-- The places `(0, 1, 1/2, 1/3, 1/4)` of `thm:block`(c), `s = 5` (`tab:block`). -/
def blk5a : Fin 5 → ZMod p := ![0, 1, (2 : ZMod p)⁻¹, (3 : ZMod p)⁻¹, (4 : ZMod p)⁻¹]

/-- The row constants `v = (1, 1, 2, 3, 4)` of `thm:block`(c), `s = 5`. -/
def blk5v : Fin 5 → ZMod p := ![1, 1, 2, 3, 4]

/-- The design `U*_5` of `thm:block`(c) (`F_0, …, F_3`; largest diagonal entry `a*_5 = 16`), in the order of the
places. -/
def blk5F : ℕ → Fin 5 → Fin 5 → ℤ := fun n =>
  if n = 0 then !![-16, 6, 2, 2, 6; 1, -8, -2, -1, -2; 1, 6, -12, -2, -3; 1, 3, 2, -12, -6; 1, 2, 1, 2, -7]
  else if n = 1 then !![0, -11, -3, -1, -1; -3, 0, 5, 1, 1; -2, -5, 0, 3, 2; -1, -4, -1, 0, 7; 0, -3, -1, 1, 0]
  else if n = 2 then !![0, 6, 0, -2, -4; 2, 0, -3, 0, 1; 0, 1, 0, -3, 1; -1, 1, 1, 0, -3; -1, 1, 0, -3, 0]
  else !![0, -1, 1, 1, -1; -1, 0, 1, 0, 0; 1, -1, 0, 2, 0; 1, 0, -2, 0, 3; 0, 0, 0, 1, 0]

/-- The partial sums `M^{(j)} = F_0 + ⋯ + F_j` of `U*_5` (checked against `blk5F` in the proof modules). -/
def blk5M : ℕ → Fin 5 → Fin 5 → ℤ := fun n =>
  if n = 0 then !![-16, 6, 2, 2, 6; 1, -8, -2, -1, -2; 1, 6, -12, -2, -3; 1, 3, 2, -12, -6; 1, 2, 1, 2, -7]
  else if n = 1 then !![-16, -5, -1, 1, 5; -2, -8, 3, 0, -1; -1, 1, -12, 1, -1; 0, -1, 1, -12, 1; 1, -1, 0, 3, -7]
  else if n = 2 then !![-16, 1, -1, -1, 1; 0, -8, 0, 0, 0; -1, 2, -12, -2, 0; -1, 0, 2, -12, -2; 0, 0, 0, 0, -7]
  else !![-16, 0, 0, 0, 0; -1, -8, 1, 0, 0; 0, 1, -12, 0, 0; 0, 0, 0, -12, 1; 0, 0, 0, 1, -7]

/-- Numerators (over `24`) of the coefficients of `N'_{c,n}` (`c` outer, `n` middle, power `k` inner). -/
def blk5cfL : List (List (List ℤ)) :=
  [[[1, -6, 13, -2], [1, -3, 8], [2, 4], [6]],
    [[-1, 3, -3, 0], [1, -2, 2], [-1, 0], [2]],
    [[10, -62, 130, -90], [-20, 80, -84], [56, -104], [-96]],
    [[-9, 78, -228, 222], [27, -144, 198], [-135, 378], [486]],
    [[12, -136, 520, -668], [-48, 352, -656], [192, -704], [-512]]]

/-- The design numerators of `thm:block`(c), `s = 5`: the solutions of identity (a) of `def:block`, in the factored
form `N_{c,5-1-n} = (z - a_c)^n N'_{c,n}`. -/
noncomputable def blk5N : Fin 5 → ℕ → (ZMod p)[X] := ndPoly blk5a (cfOf blk5cfL 24)

/-- **`thm:block`(c), `s = 5`**: the block-periodic residue sequence with `ℓ = s = 5`, places `(0, 1, 1/2, 1/3, 1/4)`,
`v = (1, 1, 2, 3, 4)` and the design `U*_5`. -/
noncomputable def blk5 (θ : ZMod p) : Gen 5 (ZMod p) :=
  blockGen blk5a θ 5 blk5v (blockF blk5F) blk5N 1

/-- The options of the checker for `s = 5` (literal; equal to `List.ofFn fun k => caOpts blk5M (Fin.rev k)`). -/
def blk5Opts : List (List (ℤ × ℤ)) :=
  [[(0, 0), (256, -30165631482), (256, -30048059643), (256, -30098325503), (256, -30047993856), (512, 30165631482), (512, 30048059643), (512, 30098325503), (512, 30047993856)],
   [(0, 0), (64, 8388476674), (64, 12683640833), (64, -201457665), (64, 4093640704), (128, -8388476674), (128, -12683640833), (128, 201457665), (128, -4093640704)],
   [(0, 0), (16, 4327734786), (16, 15991551), (16, 32767999), (16, -786176), (32, -4327734786), (32, -15991551), (32, -32767999), (32, 786176)],
   [(0, 0), (4, 8640657414), (4, -4311681029), (4, 129025), (4, 63488), (8, -8640657414), (8, 4311681029), (8, -129025), (8, -63488)],
   [(0, 0), (1, 4311810288), (1, 4294901232), (1, -16842768), (1, -272), (2, -4311810288), (2, -4294901232), (2, 16842768), (2, 272)]]

/-- The start `caStart 5` of the checker (literal). -/
def blk5St0 : ℤ := 275955859520

end Inst

end GeoSeq
