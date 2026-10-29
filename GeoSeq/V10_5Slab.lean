/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_5Defs
public import GeoSeq.SeqNet
public import GeoSeq.V7Shift

@[expose] public section

/-!
# GeoSeq stage V10-5 (part 1): `prop:liftslab` — what the Hammersley lift inherits

For any commutative ring `R` with a digit code `D : DigitCode R q` (in particular `ℤ/pℤ`) and any digital
`(0,s)`-sequence (`IsSeq0 D C`):

* `lift_first_box`: the index coordinate `v/q^m` lies in `[a q^{-K_0}, (a+1) q^{-K_0})` iff `v / q^{m-K_0} = a`.
* **`liftNet0_of_seq0`** (`prop:liftslab`(i), box form): the lift `P̂_m` is a `(0,m,s+1)`-net for every `m` (the
  paper's proof: a box with `d_0` digits in the index coordinate is one block of `q^{m-d_0}` consecutive indices,
  a `(0,m-d_0,s)`-net in the other coordinates).
* `coordE_revMat`, `coordE_truncGen`, **`liftNet0_iff`**: the box form is the digital net property of the generator
  matrices `liftGen C m` (reversal matrix first, then the leading blocks of the `C_c`); **`liftslab_i`**: both.
* **`liftslab_ii`** (`prop:liftslab`(ii)): the slab `a` (`v / q^{m-K_0} = a`) consists of the indices
  `a q^{m-K_0} + u`, `u < q^{m-K_0}`; in its last `s` coordinates it is the prefix `P_{m-K_0}` digitally shifted by
  the digits `ς_{c,n}` of the point `a` of the column-shifted sequence (`block_shift`); `slab_mem`.
* **`slab_sep`**: any lower bound on the distances of the shifted copies of `P_{m-K_0}` holds for any two points of
  one slab of the lift (the distance in `s+1` coordinates is at least the distance in the last `s`).
-/

namespace GeoSeq

open Finset Matrix

lemma nat_div_eq_iff {Q : ℕ} (hQ : 0 < Q) (v a : ℕ) : v / Q = a ↔ a * Q ≤ v ∧ v < (a + 1) * Q := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self v Q, by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hQ⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2

/-- The index coordinate `v/q^m` lies in the interval `[a q^{-K_0}, (a+1) q^{-K_0})` iff `v / q^{m-K_0} = a`. -/
theorem lift_first_box {q : ℕ} (hq : 0 < q) (m K0 a v : ℕ) (hK0 : K0 ≤ m) :
    ((a : ℝ) / (q : ℝ) ^ K0 ≤ (v : ℝ) / (q : ℝ) ^ m ∧ (v : ℝ) / (q : ℝ) ^ m < ((a : ℝ) + 1) / (q : ℝ) ^ K0) ↔
      v / q ^ (m - K0) = a := by
  have hQ : (0 : ℝ) < (q : ℝ) ^ K0 := by positivity
  have hQ' : (0 : ℝ) < (q : ℝ) ^ (m - K0) := by positivity
  have hM : (0 : ℝ) < (q : ℝ) ^ m := by positivity
  have he : (q : ℝ) ^ m = (q : ℝ) ^ (m - K0) * (q : ℝ) ^ K0 := by rw [← pow_add]; congr 1; omega
  rw [div_le_div_iff₀ hQ hM, div_lt_div_iff₀ hM hQ, he, nat_div_eq_iff (pow_pos hq _)]
  rw [← mul_assoc, mul_le_mul_iff_left₀ hQ, ← mul_assoc, mul_lt_mul_iff_left₀ hQ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

section Net

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **`prop:liftslab`(i), box form**: the Hammersley lift of a digital `(0,s)`-sequence is a `(0,m,s+1)`-net for every
`m`. -/
theorem liftNet0_of_seq0 (D : DigitCode R q) (C : Gen s R) (hseq : IsSeq0 D C) (m : ℕ) : LiftNet0 D C m := by
  intro d hd a ha
  have hsum : d 0 + ∑ c : Fin s, d c.succ = m := by rw [← Fin.sum_univ_succ]; exact hd
  have hQ : 0 < q ^ (m - d 0) := pow_pos (NeZero.pos q) _
  obtain ⟨v, ⟨hv, hcell⟩, hu⟩ := hseq (m - d 0) (a 0) (fun c => d c.succ) (by omega) (fun c => a c.succ)
    (fun c => ha c.succ)
  have hblk : ∀ w, (a 0 * q ^ (m - d 0) ≤ w ∧ w < (a 0 + 1) * q ^ (m - d 0)) ↔
      w < q ^ m ∧ w / q ^ (m - d 0) = a 0 := by
    intro w
    rw [nat_div_eq_iff hQ]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_lt_of_le h2 ?_, h1, h2⟩
      calc (a 0 + 1) * q ^ (m - d 0) ≤ q ^ d 0 * q ^ (m - d 0) :=
            Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (ha 0))
        _ = q ^ m := by rw [← pow_add]; congr 1; omega
    · rintro ⟨-, h⟩; exact h
  exact ⟨v, ⟨((hblk v).1 hv).1, ((hblk v).1 hv).2, hcell⟩,
    fun w hw => hu w ⟨(hblk w).2 ⟨hw.1, hw.2.1⟩, hw.2.2⟩⟩

lemma revMat_mulVec (m : ℕ) (w : Fin m → R) (j : Fin m) : (revMat m *ᵥ w) j = w (Fin.rev j) := by
  simp only [mulVec, dotProduct, revMat]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · rw [if_pos (by rw [Fin.val_rev]; omega), one_mul]
  · intro i _ hi
    rw [if_neg, zero_mul]
    intro h; apply hi; ext; rw [Fin.val_rev]; omega
  · intro h; exact absurd (mem_univ _) h

/-- The index coordinate of the digital lift: the reversal matrix reads the index `vecNum w` of the digit vector. -/
lemma coordE_revMat (D : DigitCode R q) (m : ℕ) (w : Fin m → R) :
    Z3NetF.coordE D.enc (revMat m) w = vecNum D m w := by
  unfold Z3NetF.coordE vecNum Z3Net.Proofs.digSum
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [revMat_mulVec]

/-- The other coordinates of the digital lift: the first `d` digits of `truncGen C m c *ᵥ w` are the cell index of the
point with index `vecNum w`. -/
lemma coordE_truncGen (D : DigitCode R q) (C : Gen s R) (m : ℕ) (w : Fin m → R) (c : Fin s) (d : ℕ)
    (hd : d ≤ m) :
    Z3NetF.coordE D.enc (truncGen C m c) w / q ^ (m - d) = cellIdx D C (vecNum D m w) c d := by
  have h1 := Z3NetF.Proofs.digSum_div_prefix q (NeZero.pos q) m
    (fun j => (D.enc ((truncGen C m c *ᵥ w) j) : ℕ)) (fun _ => (D.enc _).isLt) d hd
  have h2 : Z3NetF.coordE D.enc (truncGen C m c) w =
      Z3Net.Proofs.digSum q m (fun j => (D.enc ((truncGen C m c *ᵥ w) j) : ℕ)) := rfl
  rw [h2, h1]
  unfold cellIdx Z3Net.Proofs.digSum
  refine Finset.sum_congr rfl fun n _ => ?_
  have hv : vecNum D m w = blockIdx D m 0 w := by simp [blockIdx]
  rw [hv, seqDigit_block, seqDigit_zero, add_zero]
  simp [truncGen, mulVec, dotProduct]

/-- **The box form is the digital form** (`prop:liftslab`(i)): the lift is a `(0,m,s+1)`-net iff its generator
matrices `liftGen C m` (reversal matrix, then the leading blocks of the `C_c`) form a digital `(0,m,s+1)`-net. -/
theorem liftNet0_iff (D : DigitCode R q) (C : Gen s R) (m : ℕ) :
    LiftNet0 D C m ↔ Z3NetF.IsNet0E D.enc (liftGen C m) := by
  unfold LiftNet0 Z3NetF.IsNet0E Z3NetF.BoxExact
  refine forall_congr' fun d => forall_congr' fun hd => forall_congr' fun a => forall_congr' fun _ => ?_
  have hdm : ∀ c, d c ≤ m := Z3NetF.Proofs.le_of_sum d hd
  set P : ℕ → Prop := fun v => v / q ^ (m - d 0) = a 0 ∧ ∀ c : Fin s, cellIdx D C v c (d c.succ) = a c.succ
  have key := existsUnique_block D m 0 P
  have e1 : (∃! v : ℕ, v < q ^ m ∧ v / q ^ (m - d 0) = a 0 ∧ ∀ c : Fin s, cellIdx D C v c (d c.succ) = a c.succ) ↔
      ∃! v : ℕ, (0 * q ^ m ≤ v ∧ v < (0 + 1) * q ^ m) ∧ P v :=
    existsUnique_congr fun v => by simp [P]
  rw [e1, key]
  refine existsUnique_congr fun w => ?_
  rw [Fin.forall_fin_succ]
  simp only [liftGen, Fin.cons_zero, Fin.cons_succ, P]
  have hv : blockIdx D m 0 w = vecNum D m w := by simp [blockIdx]
  rw [hv, coordE_revMat]
  refine and_congr Iff.rfl (forall_congr' fun c => ?_)
  rw [coordE_truncGen D C m w c _ (hdm c.succ)]

/-- **`prop:liftslab`(i)**: the Hammersley lift of a digital `(0,s)`-sequence is, for every `m`, a `(0,m,s+1)`-net
(box form) and a digital `(0,m,s+1)`-net with generator matrices `liftGen C m`: the matrix reversing the `m` index
digits for the index coordinate, the `C_c` restricted to the rows and columns `0, …, m-1` for the others. -/
theorem liftslab_i (D : DigitCode R q) (C : Gen s R) (hseq : IsSeq0 D C) (m : ℕ) :
    LiftNet0 D C m ∧ Z3NetF.IsNet0E D.enc (liftGen C m) :=
  ⟨liftNet0_of_seq0 D C hseq m, (liftNet0_iff D C m).1 (liftNet0_of_seq0 D C hseq m)⟩

/-- The slab `a` of `P̂_m` with `K_0` index digits consists of the indices `a q^{m-K_0} + u`, `u < q^{m-K_0}`. -/
lemma slab_mem (m K0 v : ℕ) :
    v % q ^ (m - K0) < q ^ (m - K0) ∧ v = v / q ^ (m - K0) * q ^ (m - K0) + v % q ^ (m - K0) :=
  ⟨Nat.mod_lt _ (pow_pos (NeZero.pos q) _), by rw [mul_comm]; exact (Nat.div_add_mod _ _).symm⟩

/-- **`prop:liftslab`(ii)**: for `u < q^{m-K_0}` the index `a q^{m-K_0} + u` lies in the slab `a`; its digits are
those of `y(u)` plus the digits `ς_{c,n}` of the point `a` of the column-shifted sequence (a constant of the slab);
so in its last `s` coordinates the slab is the prefix `P_{m-K_0}` digitally shifted by `ς`. -/
theorem liftslab_ii (D : DigitCode R q) (C : Gen s R) (m K0 a u : ℕ) (hu : u < q ^ (m - K0)) :
    (a * q ^ (m - K0) + u) / q ^ (m - K0) = a ∧
    (∀ c n, seqDigit D C (a * q ^ (m - K0) + u) c n =
      seqDigit D C u c n + seqDigit D (shiftCols C (m - K0)) a c n) ∧
    ∀ c : Fin s, liftPt D C m (a * q ^ (m - K0) + u) c.succ =
      shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) u c := by
  have hQ : 0 < q ^ (m - K0) := pow_pos (NeZero.pos q) _
  refine ⟨?_, fun c n => block_shift D C (m - K0) a u hu c n, fun c => ?_⟩
  · rw [nat_div_eq_iff hQ]; constructor <;> [omega; (rw [add_mul, one_mul]; omega)]
  · simp only [liftPt, Fin.cons_succ, seqPoint, seqCoord, shPoint, shDigit]
    refine tsum_congr fun n => ?_
    rw [block_shift D C (m - K0) a u hu c n]

lemma torDist2_cons_ge {d : ℕ} (x x' : ℝ) (y y' : Fin d → ℝ) :
    Z3NetDGS.torDist2 y y' ≤ Z3NetDGS.torDist2 (Fin.cons x y : Fin (d + 1) → ℝ) (Fin.cons x' y') := by
  unfold Z3NetDGS.torDist2
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have := sq_nonneg (Z3NetDGS.torCoord x x')
  linarith

/-- **In-slab separation** (`prop:liftslab`(ii), "every bound that `lem:shift` transfers"): if every digitally shifted
copy of `P_{m-K_0}` (by the slab constants `ς`) has distances `≥ ρ`, then any two distinct points of one slab of the
lift `P̂_m` are at toroidal distance `≥ ρ`. -/
theorem slab_sep (D : DigitCode R q) (C : Gen s R) (m K0 : ℕ) (ρ : ℝ)
    (h : ∀ a u w : ℕ, u < q ^ (m - K0) → w < q ^ (m - K0) → u ≠ w →
      ρ ≤ Z3NetDGS.torDist2 (shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) u)
        (shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) w)) :
    ∀ v w : ℕ, v / q ^ (m - K0) = w / q ^ (m - K0) → v ≠ w →
      ρ ≤ Z3NetDGS.torDist2 (liftPt D C m v) (liftPt D C m w) := by
  intro v w hvw hne
  set a := v / q ^ (m - K0)
  obtain ⟨hu, hv⟩ := slab_mem (q := q) m K0 v
  obtain ⟨hu', hw⟩ := slab_mem (q := q) m K0 w
  rw [← hvw] at hw
  set u := v % q ^ (m - K0)
  set u' := w % q ^ (m - K0)
  have hne' : u ≠ u' := fun h => hne (by rw [hv, hw, h])
  have e : ∀ x, x < q ^ (m - K0) → liftPt D C m (a * q ^ (m - K0) + x) =
      Fin.cons (((a * q ^ (m - K0) + x : ℕ) : ℝ) / (q : ℝ) ^ m)
        (shPoint D C (fun c n => seqDigit D (shiftCols C (m - K0)) a c n) x) := by
    intro x hx
    funext c
    refine Fin.cases ?_ (fun c => ?_) c
    · simp [liftPt]
    · rw [(liftslab_ii D C m K0 a x hx).2.2 c, Fin.cons_succ]
  rw [hv, hw, e u hu, e u' hu']
  exact (h a u u' hu hu' hne').trans (torDist2_cons_ge _ _ _ _)

end Net

end GeoSeq
