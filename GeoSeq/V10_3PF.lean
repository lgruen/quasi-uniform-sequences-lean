/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# GeoSeq stage V10-3: explicit models of `𝔽_q = 𝔽_p[x]/(f)` with the power-basis code (`sec:primepower`)

`PF p d fc` is the ring `𝔽_p[x]/(f)` for the monic polynomial `f = x^{d+1} + ∑_{i ≤ d} fc_i x^i` (degree `r = d + 1`),
represented by the coefficient vectors `(c_0, …, c_d)` of the power basis `1, x, …, x^d`. The operations are
computable (multiplication: `∑_{i,j} c_i c'_j x^{i+j}` with `x^n` reduced modulo `f` by `xpow`), so the kernel can
evaluate them (`decide +kernel`); Mathlib's `GaloisField` is a splitting field and cannot be evaluated.

* `PF.commRing`: the ring axioms, for every `p` prime and every `fc`, by transport along the injective ring map
  `toAdj : PF p d fc → AdjoinRoot f`, `(c_i) ↦ ∑ c_i ξ^i` (`ξ` the root; injective because `f` is monic of degree
  `d + 1`). No irreducibility is needed for the ring structure.
* `PF.mkField`: a `Field` structure from an inverse map with `a · a⁻¹ = 1` for `a ≠ 0` (checked by the kernel for each
  concrete `f`, which certifies that `f` is irreducible).
* `PF.code`: **the power-basis code** of `sec:primepower`: `∑ c_i x^i ↦ ∑ c_i p^i` (`c_i ∈ {0, …, p-1}`), a
  `DigitCode (PF p d fc) (p^{d+1})`; `PF.dec` is its inverse `n ↦ (⌊n/p^i⌋ mod p)_i`.
-/

namespace GeoSeq

open Finset Polynomial

/-- The ring `𝔽_p[x]/(f)`, `f = x^{d+1} + ∑_{i ≤ d} fc_i x^i`, as coefficient vectors in the power basis. -/
structure PF (p d : ℕ) (fc : Fin (d + 1) → ZMod p) where
  /-- The coefficients `c_0, …, c_d` of `∑ c_i x^i`. -/
  v : Fin (d + 1) → ZMod p

namespace PF

variable {p d : ℕ} {fc : Fin (d + 1) → ZMod p}

@[ext] lemma ext {a b : PF p d fc} (h : a.v = b.v) : a = b := by cases a; cases b; cases h; rfl

/-- Multiplication of a coefficient vector by `x`, reduced modulo `f` (`x^{d+1} = -∑ fc_i x^i`). -/
def mulX (fc : Fin (d + 1) → ZMod p) (u : Fin (d + 1) → ZMod p) : Fin (d + 1) → ZMod p :=
  fun i => Fin.cons (α := fun _ => ZMod p) 0 (fun j : Fin d => u j.castSucc) i - u (Fin.last d) * fc i

/-- `x^n` reduced modulo `f`. -/
def xpow (fc : Fin (d + 1) → ZMod p) : ℕ → Fin (d + 1) → ZMod p
  | 0 => fun i => if (i : ℕ) = 0 then 1 else 0
  | n + 1 => mulX fc (xpow fc n)

instance : Zero (PF p d fc) := ⟨⟨0⟩⟩
instance : One (PF p d fc) := ⟨⟨xpow fc 0⟩⟩
instance : Add (PF p d fc) := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Neg (PF p d fc) := ⟨fun a => ⟨-a.v⟩⟩
instance : Sub (PF p d fc) := ⟨fun a b => ⟨a.v - b.v⟩⟩
instance : SMul ℕ (PF p d fc) := ⟨fun n a => ⟨n • a.v⟩⟩
instance : SMul ℤ (PF p d fc) := ⟨fun n a => ⟨n • a.v⟩⟩
instance : Mul (PF p d fc) := ⟨fun a b => ⟨∑ i, ∑ j, (a.v i * b.v j) • xpow fc ((i : ℕ) + j)⟩⟩
instance : Pow (PF p d fc) ℕ := ⟨fun a n => npowRec n a⟩
instance : NatCast (PF p d fc) := ⟨fun n => ⟨fun i => if (i : ℕ) = 0 then (n : ZMod p) else 0⟩⟩
instance : IntCast (PF p d fc) := ⟨fun n => ⟨fun i => if (i : ℕ) = 0 then (n : ZMod p) else 0⟩⟩

instance : DecidableEq (PF p d fc) := fun a b =>
  decidable_of_iff (∀ i, a.v i = b.v i) ⟨fun h => ext (funext h), fun h i => by rw [h]⟩

lemma zero_v : (0 : PF p d fc).v = 0 := rfl
lemma one_v : (1 : PF p d fc).v = xpow fc 0 := rfl
lemma add_v (a b : PF p d fc) : (a + b).v = a.v + b.v := rfl
lemma neg_v (a : PF p d fc) : (-a).v = -a.v := rfl
lemma sub_v (a b : PF p d fc) : (a - b).v = a.v - b.v := rfl
lemma mul_v (a b : PF p d fc) : (a * b).v = ∑ i, ∑ j, (a.v i * b.v j) • xpow fc ((i : ℕ) + j) := rfl

/-! ## The ring structure, by transport to `AdjoinRoot f` -/

/-- The polynomial `f = x^{d+1} + ∑_{i ≤ d} fc_i x^i`. -/
noncomputable def fpoly (fc : Fin (d + 1) → ZMod p) : (ZMod p)[X] :=
  X ^ (d + 1) + ∑ i : Fin (d + 1), C (fc i) * X ^ (i : ℕ)

lemma fpoly_monic : (fpoly fc).Monic := monic_X_pow_add (degree_sum_fin_lt fc)

/-- The value `∑ u_i ξ^i ∈ 𝔽_p[x]/(f)` of a coefficient vector (`ξ` the root of `f`). -/
noncomputable def toAdjV (fc : Fin (d + 1) → ZMod p) (u : Fin (d + 1) → ZMod p) : AdjoinRoot (fpoly fc) :=
  ∑ i, AdjoinRoot.of (fpoly fc) (u i) * AdjoinRoot.root (fpoly fc) ^ (i : ℕ)

/-- The ring map `PF p d fc → AdjoinRoot f`. -/
noncomputable def toAdj (a : PF p d fc) : AdjoinRoot (fpoly fc) := toAdjV fc a.v

lemma toAdjV_add (u u' : Fin (d + 1) → ZMod p) : toAdjV fc (u + u') = toAdjV fc u + toAdjV fc u' := by
  simp only [toAdjV, Pi.add_apply, map_add, add_mul, sum_add_distrib]

lemma toAdjV_zero : toAdjV fc 0 = 0 := by simp [toAdjV]

lemma toAdjV_neg (u : Fin (d + 1) → ZMod p) : toAdjV fc (-u) = -toAdjV fc u := by
  simp only [toAdjV, Pi.neg_apply, map_neg, neg_mul, sum_neg_distrib]

lemma toAdjV_smul (c : ZMod p) (u : Fin (d + 1) → ZMod p) :
    toAdjV fc (c • u) = AdjoinRoot.of (fpoly fc) c * toAdjV fc u := by
  simp only [toAdjV, Pi.smul_apply, smul_eq_mul, map_mul, mul_sum, mul_assoc]

lemma toAdjV_sum {ι : Type*} (t : Finset ι) (u : ι → Fin (d + 1) → ZMod p) :
    toAdjV fc (∑ x ∈ t, u x) = ∑ x ∈ t, toAdjV fc (u x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [toAdjV_zero]
  | insert a t ha ih => rw [sum_insert ha, sum_insert ha, toAdjV_add, ih]

lemma root_pow_succ :
    AdjoinRoot.root (fpoly fc) ^ (d + 1) =
      -∑ i : Fin (d + 1), AdjoinRoot.of (fpoly fc) (fc i) * AdjoinRoot.root (fpoly fc) ^ (i : ℕ) := by
  have h : eval₂ (AdjoinRoot.of (fpoly fc)) (AdjoinRoot.root (fpoly fc))
      (X ^ (d + 1) + ∑ i : Fin (d + 1), C (fc i) * X ^ (i : ℕ)) = 0 := AdjoinRoot.eval₂_root (fpoly fc)
  simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at h
  exact eq_neg_of_add_eq_zero_left h

lemma toAdjV_mulX (u : Fin (d + 1) → ZMod p) :
    toAdjV fc (mulX fc u) = AdjoinRoot.root (fpoly fc) * toAdjV fc u := by
  have e1 : mulX fc u = Fin.cons (α := fun _ => ZMod p) 0 (fun j : Fin d => u j.castSucc) - u (Fin.last d) • fc := by
    funext i; simp [mulX]
  rw [e1, sub_eq_add_neg, toAdjV_add, toAdjV_neg, toAdjV_smul]
  have e2 : toAdjV fc (Fin.cons (α := fun _ => ZMod p) 0 (fun j : Fin d => u j.castSucc)) =
      ∑ j : Fin d, AdjoinRoot.of (fpoly fc) (u j.castSucc) * AdjoinRoot.root (fpoly fc) ^ ((j : ℕ) + 1) := by
    rw [toAdjV, Fin.sum_univ_succ]
    simp
  have e3 : AdjoinRoot.root (fpoly fc) * toAdjV fc u =
      ∑ j : Fin d, AdjoinRoot.of (fpoly fc) (u j.castSucc) * AdjoinRoot.root (fpoly fc) ^ ((j : ℕ) + 1) +
        AdjoinRoot.of (fpoly fc) (u (Fin.last d)) * AdjoinRoot.root (fpoly fc) ^ (d + 1) := by
    rw [toAdjV, mul_sum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 1
    · exact sum_congr rfl fun j _ => by ring
    · ring
  rw [e2, e3, root_pow_succ, toAdjV]
  ring

lemma toAdjV_xpow (n : ℕ) : toAdjV fc (xpow fc n) = AdjoinRoot.root (fpoly fc) ^ n := by
  induction n with
  | zero =>
    rw [toAdjV, Fin.sum_univ_succ]
    simp [xpow]
  | succ n ih => rw [xpow, toAdjV_mulX, ih, pow_succ, mul_comm]

lemma toAdj_mul (a b : PF p d fc) : toAdj (a * b) = toAdj a * toAdj b := by
  simp only [toAdj, mul_v, toAdjV_sum, toAdjV_smul, toAdjV_xpow, map_mul]
  rw [toAdjV, toAdjV, sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [pow_add]; ring

lemma toAdj_one : toAdj (1 : PF p d fc) = 1 := by
  rw [toAdj, one_v, toAdjV_xpow, pow_zero]

lemma toAdj_natCast (n : ℕ) : toAdj (n : PF p d fc) = n := by
  show toAdjV fc (fun i => if (i : ℕ) = 0 then (n : ZMod p) else 0) = n
  rw [toAdjV, Fin.sum_univ_succ]
  simp

lemma toAdj_intCast (n : ℤ) : toAdj (n : PF p d fc) = n := by
  show toAdjV fc (fun i => if (i : ℕ) = 0 then (n : ZMod p) else 0) = n
  rw [toAdjV, Fin.sum_univ_succ]
  simp

lemma toAdj_npow (a : PF p d fc) (n : ℕ) : toAdj (a ^ n) = toAdj a ^ n := by
  induction n with
  | zero => show toAdj (npowRec 0 a) = _; rw [pow_zero]; exact toAdj_one
  | succ n ih =>
    show toAdj (npowRec n a * a) = _
    rw [toAdj_mul, pow_succ]
    exact congrArg (· * toAdj a) ih

lemma toAdj_nsmul (n : ℕ) (a : PF p d fc) : toAdj (n • a) = n • toAdj a := by
  show toAdjV fc (n • a.v) = n • toAdjV fc a.v
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) n a.v, toAdjV_smul, map_natCast, nsmul_eq_mul]

lemma toAdj_zsmul (n : ℤ) (a : PF p d fc) : toAdj (n • a) = n • toAdj a := by
  show toAdjV fc (n • a.v) = n • toAdjV fc a.v
  rw [← Int.cast_smul_eq_zsmul (ZMod p) n a.v, toAdjV_smul, map_intCast, zsmul_eq_mul]

lemma coeff_sum_fin (u : Fin (d + 1) → ZMod p) (i : Fin (d + 1)) :
    (∑ j : Fin (d + 1), C (u j) * X ^ (j : ℕ)).coeff i = u i := by
  rw [finsetSum_coeff, sum_eq_single i]
  · simp
  · intro j _ hj
    rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h' => absurd h' ?_)]
    exact fun h => hj (Fin.ext h.symm)
  · simp

variable [Fact p.Prime]

lemma fpoly_degree : (fpoly fc).degree = ((d + 1 : ℕ) : WithBot ℕ) := by
  rw [fpoly, degree_add_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact degree_sum_fin_lt fc

lemma toAdjV_inj (u : Fin (d + 1) → ZMod p) (h : toAdjV fc u = 0) : u = 0 := by
  by_contra hu
  have hP : (∑ j : Fin (d + 1), C (u j) * X ^ (j : ℕ)) ≠ 0 := by
    intro h0
    apply hu; funext i
    have := congrArg (fun P : (ZMod p)[X] => P.coeff (i : ℕ)) h0
    rwa [coeff_sum_fin, coeff_zero] at this
  have hdeg : (∑ j : Fin (d + 1), C (u j) * X ^ (j : ℕ)).degree < (fpoly fc).degree := by
    rw [fpoly_degree]; exact degree_sum_fin_lt u
  refine AdjoinRoot.mk_ne_zero_of_degree_lt fpoly_monic hP hdeg ?_
  rw [← h, toAdjV, map_sum]
  simp only [map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]

lemma toAdj_injective : Function.Injective (toAdj : PF p d fc → AdjoinRoot (fpoly fc)) := by
  intro a b h
  have h1 : toAdjV fc (a.v - b.v) = 0 := by
    rw [sub_eq_add_neg, toAdjV_add, toAdjV_neg, ← sub_eq_add_neg]; exact sub_eq_zero.mpr h
  exact ext (sub_eq_zero.mp (toAdjV_inj _ h1))

/-- **The ring `𝔽_p[x]/(f)`** in the power-basis model (every monic `f`, `p` prime). -/
noncomputable instance commRing : CommRing (PF p d fc) :=
  Function.Injective.commRing toAdj toAdj_injective (by simp [toAdj, toAdjV_zero, zero_v]) toAdj_one
    (fun a b => toAdjV_add a.v b.v) toAdj_mul (fun a => toAdjV_neg a.v)
    (fun a b => by
      show toAdjV fc (a.v - b.v) = toAdjV fc a.v - toAdjV fc b.v
      rw [sub_eq_add_neg, toAdjV_add, toAdjV_neg, ← sub_eq_add_neg])
    toAdj_nsmul toAdj_zsmul toAdj_npow toAdj_natCast toAdj_intCast

/-- `PF p d fc` has characteristic `p`. -/
instance charP : CharP (PF p d fc) p := ⟨fun x => by
  rw [← CharP.cast_eq_zero_iff (ZMod p) p x]
  constructor
  · intro h
    have := congrArg (fun a : PF p d fc => a.v 0) h
    exact this
  · intro h
    apply ext; funext i
    show (if (i : ℕ) = 0 then (x : ZMod p) else 0) = 0
    split_ifs <;> simp [h]⟩

/-- A field structure on `PF p d fc` from an inverse map (`0⁻¹ = 0`, `a a⁻¹ = 1` for `a ≠ 0`); for a concrete `f`
the hypotheses are checked by the kernel, which certifies that `f` is irreducible over `𝔽_p`. -/
noncomputable abbrev mkField (inv : PF p d fc → PF p d fc) (h0 : inv 0 = 0) (h01 : (0 : PF p d fc) ≠ 1)
    (h : ∀ a, a ≠ 0 → a * inv a = 1) : Field (PF p d fc) where
  inv := inv
  mul_inv_cancel := h
  inv_zero := h0
  exists_pair_ne := ⟨0, 1, h01⟩
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end PF

/-! ## The power-basis code -/

namespace PF

variable {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [NeZero p]

/-- The code `∑ c_i x^i ↦ ∑ c_i p^i` (`sec:primepower`). -/
def encN (a : PF p d fc) : ℕ := ∑ i : Fin (d + 1), (a.v i).val * p ^ (i : ℕ)

/-- The inverse of the code: the element whose coefficient `i` is the base-`p` digit `⌊n/p^i⌋ mod p` of `n`. -/
def dec (n : ℕ) : PF p d fc := ⟨fun i => ((n / p ^ (i : ℕ) % p : ℕ) : ZMod p)⟩

/-- The coefficients as digits `Fin p`. -/
def digs (a : PF p d fc) : Fin (d + 1) → Fin p := fun i => ⟨(a.v i).val, ZMod.val_lt _⟩

lemma encN_eq (a : PF p d fc) : encN a = (finFunctionFinEquiv (digs a) : ℕ) := by
  rw [finFunctionFinEquiv_apply]; rfl

lemma encN_lt (a : PF p d fc) : encN a < p ^ (d + 1) := by
  rw [encN_eq]; exact (finFunctionFinEquiv (digs a)).isLt

lemma dec_encN (a : PF p d fc) : dec (encN a) = a := by
  ext i
  have h : (finFunctionFinEquiv.symm (finFunctionFinEquiv (digs a)) i : ℕ) = (a.v i).val := by
    rw [Equiv.symm_apply_apply]; rfl
  have h2 : (finFunctionFinEquiv.symm (finFunctionFinEquiv (digs a)) i : ℕ) =
      encN a / p ^ (i : ℕ) % p := by rw [encN_eq]; rfl
  show ((encN a / p ^ (i : ℕ) % p : ℕ) : ZMod p) = a.v i
  rw [← h2, h, ZMod.natCast_zmod_val]

lemma encN_dec (n : ℕ) (hn : n < p ^ (d + 1)) : encN (dec n : PF p d fc) = n := by
  have h1 : digs (dec n : PF p d fc) = finFunctionFinEquiv.symm ⟨n, hn⟩ := by
    funext i; apply Fin.ext
    show ((n / p ^ (i : ℕ) % p : ℕ) : ZMod p).val = n / p ^ (i : ℕ) % p
    rw [ZMod.val_natCast, Nat.mod_mod]
  rw [encN_eq, h1, Equiv.apply_symm_apply]

/-- **The power-basis code** of `𝔽_p[x]/(f)` (`sec:primepower`): `∑ c_i x^i ↦ ∑ c_i p^i`. -/
def code : DigitCode (PF p d fc) (p ^ (d + 1)) where
  enc :=
    { toFun := fun a => ⟨encN a, encN_lt a⟩
      invFun := fun n => dec n
      left_inv := fun a => dec_encN a
      right_inv := fun n => Fin.ext (encN_dec n n.isLt) }
  enc_zero := by
    show encN (0 : PF p d fc) = 0
    simp [encN, zero_v]

instance : Fintype (PF p d fc) :=
  Fintype.ofEquiv (Fin (d + 1) → ZMod p) ⟨PF.mk, PF.v, fun _ => rfl, fun _ => rfl⟩

lemma mem_elems_aux (a : PF p d fc) : a ∈ (List.range (p ^ (d + 1))).map dec :=
  List.mem_map.mpr ⟨encN a, List.mem_range.mpr (encN_lt a), dec_encN a⟩

/-- Universal quantification over `PF` from quantification over the codes (kernel-friendly). -/
lemma forall_of_dec {P : PF p d fc → Prop} (h : ∀ n : Fin (p ^ (d + 1)), P (dec n)) : ∀ a, P a := fun a => by
  have := h ⟨encN a, encN_lt a⟩
  rwa [dec_encN] at this

end PF

end GeoSeq
