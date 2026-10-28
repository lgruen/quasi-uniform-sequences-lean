/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs
public import Z3Net.FMain
public import Z3Net.FBasic
public import Z3Net.DShift

@[expose] public section

/-!
# GeoSeq stage S1: sequences and nets (`sec:prelim`, the remark after `lem:nie`)

* The block `{y(v) : k q^m ≤ v < (k+1) q^m}` is a digital shift of the prefix `P_m`: for `v < q^m`,
  digit `n` of coordinate `c` of `y(k q^m + v)` is digit `n` of `y(v)` plus a constant that depends
  only on `k, c, n` (`block_shift`; the constant is digit `n` of the point `k` of the sequence with
  the columns shifted by `m`).
* A digital shift maps elementary boxes of each shape bijectively onto boxes of the same shape
  (`cond_shift`, the argument of geo `lem:shift`, `Z3NetF.shift_net`, redone over a general digit
  code `DigitCode R q`: geo's `dshiftPt` is stated over `ℤ/qℤ` only; the geo digit lemmas
  `digSum_digit`, `digSum_recon`, `digSum_div_prefix` are reused).
* Hence every block is a `(0,m,s)`-net iff the prefix is, iff the truncated generator matrices form a
  `(0,m,s)`-net in the sense of geo `lem:nie` (`blockNet0_iff`), and
  `IsSeq0 ↔ ∀ m, IsNet0E (truncGen C m)` (`isSeq0_iff_trunc`).
-/

namespace GeoSeq

open Finset Matrix

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-! ## Index digits -/

lemma idxDigit_eq_zero (D : DigitCode R q) (v k : ℕ) (h : v / q ^ k % q = 0) :
    idxDigit D v k = 0 := by
  unfold idxDigit
  have : (⟨v / q ^ k % q, Nat.mod_lt _ (NeZero.pos q)⟩ : Fin q) = D.enc 0 :=
    Fin.ext (by show v / q ^ k % q = _; rw [h, D.enc_zero])
  rw [this, Equiv.symm_apply_apply]

omit [NeZero q] in
lemma digit_high (v k : ℕ) (h : v < q ^ k) : v / q ^ k % q = 0 := by
  rw [Nat.div_eq_of_lt h, Nat.zero_mod]

lemma digit_beyond (v k : ℕ) (h : v < k) : v / q ^ k % q = 0 := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · have : q = 1 := by have := NeZero.pos q; omega
    subst this; exact Nat.mod_one _
  · apply digit_high
    calc v < k := h
      _ < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ q ^ k := Nat.pow_le_pow_left hq k

/-- `seqDigit` may be summed over any range beyond which the index digits vanish. -/
lemma seqDigit_eq_range (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) (n M : ℕ)
    (hM : ∀ k, M ≤ k → idxDigit D v k = 0) :
    seqDigit D C v c n = ∑ k ∈ range M, C c n k * idxDigit D v k := by
  unfold seqDigit
  have key : ∀ A B : ℕ, A ≤ B → (∀ k, A ≤ k → idxDigit D v k = 0) →
      ∑ k ∈ range A, C c n k * idxDigit D v k = ∑ k ∈ range B, C c n k * idxDigit D v k := by
    intro A B hAB hA
    apply Finset.sum_subset (Finset.range_subset_range.mpr hAB)
    intro k _ hk'
    simp only [mem_range, not_lt] at hk'
    rw [hA k hk', mul_zero]
  have h1 : ∀ k, v + 1 ≤ k → idxDigit D v k = 0 :=
    fun k hk => idxDigit_eq_zero D v k (digit_beyond v k (by omega))
  rw [key (v + 1) (max (v + 1) M) (le_max_left _ _) h1,
    key M (max (v + 1) M) (le_max_right _ _) hM]

/-! ## The index of a vector inside a block -/

/-- The integer with little-endian digits `enc(w_0), …, enc(w_{m-1})`. -/
def vecNum (D : DigitCode R q) (m : ℕ) (w : Fin m → R) : ℕ :=
  Z3Net.Proofs.digSum q m (fun j => (D.enc (w (Fin.rev j)) : ℕ))

/-- The index `k q^m + vecNum w` of the vector `w` in block `k`. -/
def blockIdx (D : DigitCode R q) (m k : ℕ) (w : Fin m → R) : ℕ := k * q ^ m + vecNum D m w

omit [NeZero q] in
lemma vecNum_lt (D : DigitCode R q) (m : ℕ) (w : Fin m → R) : vecNum D m w < q ^ m :=
  Z3Net.Proofs.digSum_lt q m _ (fun _ => (D.enc _).isLt)

lemma vecNum_digit (D : DigitCode R q) (m : ℕ) (w : Fin m → R) (i : Fin m) :
    vecNum D m w / q ^ (i : ℕ) % q = (D.enc (w i) : ℕ) := by
  have h := Z3NetF.Proofs.digSum_digit (NeZero.pos q) m (fun j => (D.enc (w (Fin.rev j)) : ℕ))
    (fun _ => (D.enc _).isLt) (Fin.rev i)
  have e : m - 1 - ((Fin.rev i : Fin m) : ℕ) = (i : ℕ) := by
    rw [Fin.val_rev]; have := i.isLt; omega
  rw [e, Fin.rev_rev] at h
  exact h

lemma blockIdx_lo (D : DigitCode R q) (m k : ℕ) (w : Fin m → R) (i : Fin m) :
    blockIdx D m k w / q ^ (i : ℕ) % q = (D.enc (w i) : ℕ) := by
  have hi := i.isLt
  have hpos : 0 < q ^ (i : ℕ) := pow_pos (NeZero.pos q) _
  have e0 : q ^ m = q ^ (i : ℕ) * (q ^ (m - 1 - (i : ℕ)) * q) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have e1 : k * q ^ m = q ^ (i : ℕ) * (k * q ^ (m - 1 - (i : ℕ)) * q) := by
    rw [e0]; ring
  unfold blockIdx
  rw [e1, Nat.mul_add_div hpos, Nat.add_comm, Nat.add_mul_mod_self_right]
  exact vecNum_digit D m w i

lemma blockIdx_hi (D : DigitCode R q) (m k : ℕ) (w : Fin m → R) (j : ℕ) :
    blockIdx D m k w / q ^ (m + j) % q = k / q ^ j % q := by
  have hpos : 0 < q ^ m := pow_pos (NeZero.pos q) _
  unfold blockIdx
  rw [pow_add, ← Nat.div_div_eq_div_mul, mul_comm k, Nat.mul_add_div hpos,
    Nat.div_eq_of_lt (vecNum_lt D m w), add_zero]

lemma idxDigit_block_lo (D : DigitCode R q) (m k : ℕ) (w : Fin m → R) (i : Fin m) :
    idxDigit D (blockIdx D m k w) i = w i := by
  unfold idxDigit
  have : (⟨blockIdx D m k w / q ^ (i : ℕ) % q, Nat.mod_lt _ (NeZero.pos q)⟩ : Fin q) = D.enc (w i) :=
    Fin.ext (blockIdx_lo D m k w i)
  rw [this, Equiv.symm_apply_apply]

lemma idxDigit_block_hi (D : DigitCode R q) (m k : ℕ) (w : Fin m → R) (j : ℕ) :
    idxDigit D (blockIdx D m k w) (m + j) = idxDigit D k j := by
  unfold idxDigit
  congr 2
  exact blockIdx_hi D m k w j

omit [NeZero q] in
lemma blockIdx_mem (D : DigitCode R q) (m k : ℕ) (w : Fin m → R) :
    k * q ^ m ≤ blockIdx D m k w ∧ blockIdx D m k w < (k + 1) * q ^ m := by
  have := vecNum_lt D m w
  unfold blockIdx
  constructor
  · omega
  · rw [add_mul, one_mul]; omega

lemma blockIdx_inj (D : DigitCode R q) (m k : ℕ) {w w' : Fin m → R}
    (h : blockIdx D m k w = blockIdx D m k w') : w = w' := by
  funext i
  have h1 := blockIdx_lo D m k w i
  rw [h, blockIdx_lo D m k w' i] at h1
  exact D.enc.injective (Fin.ext h1.symm)

lemma blockIdx_surj (D : DigitCode R q) (m k v : ℕ) (hv : k * q ^ m ≤ v ∧ v < (k + 1) * q ^ m) :
    ∃ w, blockIdx D m k w = v := by
  set r := v - k * q ^ m with hr
  have hrlt : r < q ^ m := by rw [add_mul, one_mul] at hv; omega
  refine ⟨fun i => D.enc.symm ⟨r / q ^ (i : ℕ) % q, Nat.mod_lt _ (NeZero.pos q)⟩, ?_⟩
  unfold blockIdx vecNum
  have e : (fun j : Fin m => ((D.enc (D.enc.symm
      ⟨r / q ^ ((Fin.rev j : Fin m) : ℕ) % q, Nat.mod_lt _ (NeZero.pos q)⟩) : Fin q) : ℕ)) =
      (fun j : Fin m => r / q ^ (m - 1 - (j : ℕ)) % q) := by
    funext j
    rw [Equiv.apply_symm_apply, Fin.val_rev, show m - ((j : ℕ) + 1) = m - 1 - (j : ℕ) by omega]
  rw [e, Z3NetF.Proofs.digSum_recon (NeZero.pos q) m r hrlt]
  omega

/-- `∃!` over a block of indices is `∃!` over the index vectors. -/
lemma existsUnique_block (D : DigitCode R q) (m k : ℕ) (P : ℕ → Prop) :
    (∃! v : ℕ, (k * q ^ m ≤ v ∧ v < (k + 1) * q ^ m) ∧ P v) ↔
      ∃! w : Fin m → R, P (blockIdx D m k w) := by
  constructor
  · rintro ⟨v, ⟨hv, hP⟩, hu⟩
    obtain ⟨w, rfl⟩ := blockIdx_surj D m k v hv
    exact ⟨w, hP, fun w' hw' => blockIdx_inj D m k (hu _ ⟨blockIdx_mem D m k w', hw'⟩)⟩
  · rintro ⟨w, hP, hu⟩
    refine ⟨blockIdx D m k w, ⟨blockIdx_mem D m k w, hP⟩, ?_⟩
    rintro v ⟨hv, hPv⟩
    obtain ⟨w', rfl⟩ := blockIdx_surj D m k v hv
    rw [hu w' hPv]

/-! ## Digits of a block point -/

/-- Digit `n` of `y(blockIdx w)` = digit `n` of the prefix point with index vector `w` plus the
digit `n` of the point `k` of the column-shifted sequence. -/
lemma seqDigit_block (D : DigitCode R q) (C : Gen s R) (m k : ℕ) (w : Fin m → R) (c : Fin s)
    (n : ℕ) : seqDigit D C (blockIdx D m k w) c n =
      (∑ j : Fin m, C c n j * w j) + seqDigit D (shiftCols C m) k c n := by
  rw [seqDigit_eq_range D C _ c n (m + (k + 1)), Finset.sum_range_add]
  · congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun x => C c n x * idxDigit D (blockIdx D m k w) x) m]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [idxDigit_block_lo]
    · unfold seqDigit shiftCols
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [idxDigit_block_hi]
  · intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = m + j' := ⟨j - m, by omega⟩
    rw [idxDigit_block_hi]
    exact idxDigit_eq_zero D k j' (digit_beyond k j' (by omega))

/-- The first point `y(0)` has all digits `0`. -/
lemma seqDigit_zero (D : DigitCode R q) (C : Gen s R) (c : Fin s) (n : ℕ) :
    seqDigit D C 0 c n = 0 := by
  unfold seqDigit
  simp [idxDigit_eq_zero D 0 0 (by simp)]

/-! ## Boxes under a digital shift -/

/-- A vector of `R^m` extended by `0` to all of `ℕ`. -/
def vecN {m : ℕ} (x : Fin m → R) (n : ℕ) : R := if h : n < m then x ⟨n, h⟩ else 0

lemma vecN_mulVec (C : Gen s R) (m : ℕ) (w : Fin m → R) (c : Fin s) (n : ℕ) (hn : n < m) :
    vecN (truncGen C m c *ᵥ w) n = ∑ j : Fin m, C c n j * w j := by
  simp [vecN, hn, truncGen, mulVec, dotProduct]

/-- Digit `n` (most significant first) of `a < q^d`, as an element of `R`. -/
def digOf (D : DigitCode R q) (d a n : ℕ) : R :=
  D.enc.symm ⟨a / q ^ (d - 1 - n) % q, Nat.mod_lt _ (NeZero.pos q)⟩

lemma digSum_enc_eq_iff (D : DigitCode R q) (d a : ℕ) (ha : a < q ^ d) (f : Fin d → R) :
    Z3Net.Proofs.digSum q d (fun n => (D.enc (f n) : ℕ)) = a ↔
      ∀ n : Fin d, f n = digOf D d a n := by
  constructor
  · intro h n
    have := Z3NetF.Proofs.digSum_digit (NeZero.pos q) d (fun n => (D.enc (f n) : ℕ))
      (fun _ => (D.enc _).isLt) n
    rw [h] at this
    unfold digOf
    rw [Equiv.eq_symm_apply]
    exact Fin.ext this.symm
  · intro h
    have e : (fun n : Fin d => (D.enc (f n) : ℕ)) = fun n : Fin d => a / q ^ (d - 1 - (n : ℕ)) % q := by
      funext n; rw [h n]; unfold digOf; rw [Equiv.apply_symm_apply]
    rw [e]
    exact Z3NetF.Proofs.digSum_recon (NeZero.pos q) d a ha

lemma digOf_digSum (D : DigitCode R q) (d : ℕ) (g : Fin d → R) (n : Fin d) :
    digOf D d (Z3Net.Proofs.digSum q d (fun n => (D.enc (g n) : ℕ))) n = g n := by
  have := Z3NetF.Proofs.digSum_digit (NeZero.pos q) d (fun n => (D.enc (g n) : ℕ))
    (fun _ => (D.enc _).isLt) n
  unfold digOf
  rw [Equiv.symm_apply_eq]
  exact Fin.ext this

/-- **The shift step of `lem:shift`** (geo `Z3NetF.shift_net`, over a general digit code): adding
constants `u` (resp. `u'`) to the digits maps the box `a` of shape `d` to a box `a'` of the same
shape, simultaneously for all digit families `X`. -/
lemma cond_shift (D : DigitCode R q) (d : Fin s → ℕ) (u u' : Fin s → ℕ → R) (a : Fin s → ℕ)
    (ha : ∀ c, a c < q ^ d c) :
    ∃ a' : Fin s → ℕ, (∀ c, a' c < q ^ d c) ∧ ∀ X : Fin s → ℕ → R,
      (∀ c, Z3Net.Proofs.digSum q (d c) (fun n => (D.enc (X c n + u c n) : ℕ)) = a c) ↔
      (∀ c, Z3Net.Proofs.digSum q (d c) (fun n => (D.enc (X c n + u' c n) : ℕ)) = a' c) := by
  refine ⟨fun c => Z3Net.Proofs.digSum q (d c)
      (fun n => (D.enc (digOf D (d c) (a c) n - u c n + u' c n) : ℕ)),
    fun c => Z3Net.Proofs.digSum_lt q _ _ (fun _ => (D.enc _).isLt), fun X => ?_⟩
  refine forall_congr' fun c => ?_
  rw [digSum_enc_eq_iff D _ _ (ha c) (fun n : Fin (d c) => X c n + u c n),
    digSum_enc_eq_iff D _ _ (Z3Net.Proofs.digSum_lt q _ _ (fun _ => (D.enc _).isLt))
      (fun n : Fin (d c) => X c n + u' c n)]
  refine forall_congr' fun n => ?_
  rw [digOf_digSum]
  constructor
  · intro h; rw [← h]; ring
  · intro h; linear_combination h

/-- **Blocks and prefixes** (`sec:prelim`): block `k` of `q^m` points is a `(0,m,s)`-net iff the
truncated generator matrices form a `(0,m,s)`-net (geo `lem:nie` form `Z3NetF.IsNet0E`). -/
theorem blockNet0_iff (D : DigitCode R q) (C : Gen s R) (m k : ℕ) :
    BlockNet0 D C m k ↔ Z3NetF.IsNet0E D.enc (truncGen C m) := by
  unfold BlockNet0 Z3NetF.IsNet0E Z3NetF.BoxExact
  refine forall_congr' fun d => forall_congr' fun hd => ?_
  have hdm : ∀ c, d c ≤ m := Z3NetF.Proofs.le_of_sum d hd
  have hB : ∀ a : Fin s → ℕ,
      (∃! v : ℕ, (k * q ^ m ≤ v ∧ v < (k + 1) * q ^ m) ∧ ∀ c, cellIdx D C v c (d c) = a c) ↔
      ∃! w : Fin m → R, ∀ c, Z3Net.Proofs.digSum q (d c) (fun n => (D.enc
        (vecN (truncGen C m c *ᵥ w) n + seqDigit D (shiftCols C m) k c n) : ℕ)) = a c := by
    intro a
    rw [existsUnique_block D m k]
    refine existsUnique_congr fun w => forall_congr' fun c => ?_
    have hfun : (fun n : Fin (d c) => (D.enc (seqDigit D C (blockIdx D m k w) c n) : ℕ)) =
        (fun n : Fin (d c) => (D.enc (vecN (truncGen C m c *ᵥ w) n +
          seqDigit D (shiftCols C m) k c n) : ℕ)) := by
      funext n
      rw [seqDigit_block, vecN_mulVec C m w c n (lt_of_lt_of_le n.isLt (hdm c))]
    show Z3Net.Proofs.digSum q (d c) _ = a c ↔ _
    rw [hfun]
  have hE : ∀ a : Fin s → ℕ,
      (∃! w : Fin m → R, ∀ c, Z3NetF.coordE D.enc (truncGen C m c) w / q ^ (m - d c) = a c) ↔
      ∃! w : Fin m → R, ∀ c, Z3Net.Proofs.digSum q (d c) (fun n => (D.enc
        (vecN (truncGen C m c *ᵥ w) n + (fun _ _ => (0 : R)) c n) : ℕ)) = a c := by
    intro a
    refine existsUnique_congr fun w => forall_congr' fun c => ?_
    have h1 := Z3NetF.Proofs.digSum_div_prefix q (NeZero.pos q) m
      (fun j => (D.enc ((truncGen C m c *ᵥ w) j) : ℕ)) (fun _ => (D.enc _).isLt) (d c) (hdm c)
    have h2 : Z3NetF.coordE D.enc (truncGen C m c) w =
        Z3Net.Proofs.digSum q m (fun j => (D.enc ((truncGen C m c *ᵥ w) j) : ℕ)) := rfl
    rw [h2, h1]
    have hfun : (fun j : Fin (d c) => (D.enc ((truncGen C m c *ᵥ w)
          ⟨j, lt_of_lt_of_le j.isLt (hdm c)⟩) : ℕ)) =
        (fun n : Fin (d c) => (D.enc (vecN (truncGen C m c *ᵥ w) n + (fun _ _ => (0 : R)) c n) : ℕ)) := by
      funext n
      simp only [vecN, lt_of_lt_of_le n.isLt (hdm c), dite_true, add_zero]
    rw [hfun]
  constructor
  · intro h a ha
    obtain ⟨a', ha', hiff⟩ := cond_shift D d (fun _ _ => 0) (fun c n => seqDigit D (shiftCols C m) k c n) a ha
    rw [hE, existsUnique_congr fun w => hiff (fun c n => vecN (truncGen C m c *ᵥ w) n)]
    exact (hB a').1 (h a' ha')
  · intro h a ha
    obtain ⟨a', ha', hiff⟩ := cond_shift D d (fun c n => seqDigit D (shiftCols C m) k c n) (fun _ _ => 0) a ha
    rw [hB, existsUnique_congr fun w => hiff (fun c n => vecN (truncGen C m c *ᵥ w) n)]
    exact (hE a').1 (h a' ha')

/-- **`IsSeq0` ↔ prefixes are nets** (`sec:prelim`): a digital sequence is a `(0,s)`-sequence iff for
every `m` the truncated generator matrices form a `(0,m,s)`-net (geo `Z3NetF.IsNet0E`); every block
is a digital shift of the prefix (`block_shift`) and has the same box minors. -/
theorem isSeq0_iff_trunc (D : DigitCode R q) (C : Gen s R) :
    IsSeq0 D C ↔ ∀ m : ℕ, Z3NetF.IsNet0E D.enc (truncGen C m) :=
  ⟨fun h m => (blockNet0_iff D C m 0).1 (h m 0), fun h m k => (blockNet0_iff D C m k).2 (h m)⟩

/-- **Blocks are digital shifts of the prefix** (`sec:prelim`): for `v < q^m`, digit `n` of
coordinate `c` of `y(k q^m + v)` is digit `n` of `y(v)` plus digit `n` of the point `k` of the
column-shifted sequence `shiftCols C m` (a constant of the block). -/
theorem block_shift (D : DigitCode R q) (C : Gen s R) (m k v : ℕ) (hv : v < q ^ m) (c : Fin s)
    (n : ℕ) :
    seqDigit D C (k * q ^ m + v) c n = seqDigit D C v c n + seqDigit D (shiftCols C m) k c n := by
  obtain ⟨w, hw⟩ := blockIdx_surj D m 0 v ⟨by simp, by simpa using hv⟩
  have hk : k * q ^ m + v = blockIdx D m k w := by
    rw [← hw]; unfold blockIdx; ring
  rw [hk, ← hw, seqDigit_block, seqDigit_block, seqDigit_zero, add_zero]

end GeoSeq
