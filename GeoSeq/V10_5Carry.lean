/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_5Defs
public import GeoSeq.V95Gen
public import GeoSeq.V93Carry
public import GeoSeq.V9Res

@[expose] public section

/-!
# GeoSeq stage V10-5 (part 2): `prop:liftcarry` — close pairs across a carry of the index

Scrambled frames `C_c = L_c P_{a_c}` over `ℤ/pℤ` (`scrGen a L`: any lower-triangular `L_c`, nonsingular or not), any
digital shift `ς` (`liftPtSh`), places `a_c ∈ {0} ∪ μ_n` (`a_c = 0 ∨ a_c^n = 1`; `n ∣ p - 1` and distinct places are
not needed for the inequality).

* **`liftD_identity`** (the algebraic core, Frobenius): `∑_{t < n p^r} z^t = (z-1)^{p^r-1} (1 + z + ⋯ + z^{n-1})^{p^r}`
  in `𝔽_p[z]`; with `ℓ + 1 = n p^r` the index difference is `D = V_j - V_i = z^k (1 + ⋯ + z^ℓ)`
  (`idxPolyP_carry_diff`), i.e. `D = z^k (z^n-1)^{p^r}/(z-1)`.
* **`liftD_dvd`** (orders of vanishing): `(z - a)^{ord(a)} ∣ D` with `ord(0) = k`, `ord(1) = p^r - 1`, and
  `ord(ζ) = p^r` for every other `n`-th root of unity `ζ` (`liftOrd`) — one more than the paper's `p^r - 1` at `ζ ≠ 1`.
* `genY_scrGen`, `genY_scrGen_vanish`: a frame row reads Taylor coefficients, so the first `ord(a_c)` digits of
  coordinate `c` of `D` vanish.
* **`liftcarry_pair`**: the two indices `i = (p^ℓ-1) p^k`, `j = p^{k+ℓ} = i + p^k < p^m` satisfy
  `‖ŷ_i - ŷ_j‖_T² ≤ (p^k/p^m)² + ∑_c p^{-2 ord(a_c)}`.
* **`liftcarry_sharp`** (`δ(P̂_m)²` ≤ the same), **`liftcarry`** (`prop:liftcarry` as stated: distinct places,
  `δ(P̂_m)² ≤ p^{2(k-m)} + [0∈A] p^{-2k} + |A∖{0}| p^{-2(p^r-1)}`).
* **Closed forms at `m = s p^r`**: `liftcarry_closed0` (`A ⊆ {0} ∪ μ_{s-1}`, `s ≥ 2`) and `liftcarry_closedMu`
  (`A ⊆ μ_s`): `δ(P̂_m) ≤ √(s+p²) p^{-p^r} = √(s+p²) N^{-1/s}` (sharper than the paper's constants for `s ≥ 3`);
  normalized: `δ N^{1/(s+1)} ≤ √(s+p²) p^{-p^r/(s+1)}` (`liftcarry_closed0_norm`, `liftcarry_closedMu_norm`); the
  paper's constants `√(2+(s-1)p²)` and `√(1+sp²)`: `liftcarry_gamma0`, `liftcarry_gammaMu`.
* **`lift_not_wellsep`**: for these place sets and every scramble and shift, `inf_m δ(P̂_m) N^{1/(s+1)} = 0`; for the
  places `{0,1}` (`s = 2`): `lift01_not_wellsep`, and the residue and staggered residue sequences
  (`lift_resSeq01_not_wellsep`, `lift_resStar01_not_wellsep`).
-/

namespace GeoSeq

open Finset Polynomial

section Poly

variable {p : ℕ} [Fact p.Prime]

/-- **The Frobenius identity of `prop:liftcarry`**: `∑_{t < n p^r} z^t = (z-1)^{p^r-1} (∑_{t<n} z^t)^{p^r}` in `𝔽_p[z]`
(both sides times `z - 1` are `z^{np^r} - 1 = (z^n - 1)^{p^r}`). -/
theorem liftD_identity (n r : ℕ) :
    ∑ t ∈ range (n * p ^ r), (X : (ZMod p)[X]) ^ t =
      (X - 1) ^ (p ^ r - 1) * (∑ t ∈ range n, (X : (ZMod p)[X]) ^ t) ^ (p ^ r) := by
  have hX : (X - 1 : (ZMod p)[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ZMod p)
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  apply mul_right_cancel₀ hX
  rw [geom_sum_mul]
  calc (X : (ZMod p)[X]) ^ (n * p ^ r) - 1 = (X ^ n - 1) ^ (p ^ r) := by
        rw [sub_pow_char_pow, one_pow, ← pow_mul]
    _ = ((∑ t ∈ range n, (X : (ZMod p)[X]) ^ t) * (X - 1)) ^ (p ^ r) := by rw [geom_sum_mul]
    _ = (X - 1) ^ (p ^ r - 1 + 1) * (∑ t ∈ range n, (X : (ZMod p)[X]) ^ t) ^ (p ^ r) := by
        rw [Nat.sub_add_cancel hpr, mul_pow, mul_comm]
    _ = _ := by ring

/-- **The orders of vanishing** (`prop:liftcarry`): `D = z^k (z-1)^{p^r-1} H^{p^r}`, `H = ∑_{t<n} z^t`, is divisible by
`(z - a)^{ord(a)}` for every place `a = 0` or `a^n = 1`: `ord(0) = k`, `ord(1) = p^r - 1`, `ord(ζ) = p^r` for
`ζ^n = 1`, `ζ ≠ 1` (`H(ζ) = 0`). -/
theorem liftD_dvd (n r k : ℕ) (a : ZMod p) (ha : a = 0 ∨ a ^ n = 1) :
    (X - C a) ^ liftOrd p r k a ∣
      X ^ k * ((X - 1) ^ (p ^ r - 1) * (∑ t ∈ range n, (X : (ZMod p)[X]) ^ t) ^ (p ^ r)) := by
  unfold liftOrd
  by_cases h0 : a = 0
  · rw [if_pos h0, h0, map_zero, sub_zero]; exact dvd_mul_right _ _
  rw [if_neg h0]
  have han : a ^ n = 1 := ha.resolve_left h0
  by_cases h1 : a = 1
  · rw [if_pos h1, h1, map_one]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  rw [if_neg h1]
  have hroot : X - C a ∣ ∑ t ∈ range n, (X : (ZMod p)[X]) ^ t := by
    rw [dvd_iff_isRoot, IsRoot.def, eval_finset_sum]
    simp only [eval_pow, eval_X]
    have := geom_sum_mul a n
    rw [han, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h1)
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hroot _) _) _

/-- The index polynomial of `∑_{t<N} b_t p^t` (digits `b_t < p`) is `∑_{t<N} b_t z^t`. -/
lemma idxPolyP_of_digits (N : ℕ) (b : ℕ → ℕ) (hb : ∀ t, b t < p) :
    idxPolyP p (∑ t ∈ range N, b t * p ^ t) = ∑ t ∈ range N, C ((b t : ℕ) : ZMod p) * X ^ t := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  ext t
  have hd := natDigits_sum hp1 N b hb t
  rw [coeff_idxPolyP, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [mem_range]
  by_cases ht : t < ∑ t ∈ range N, b t * p ^ t + 1
  · rw [if_pos ht, hd]; split_ifs <;> simp
  · rw [if_neg ht]
    have hlt : ∑ t ∈ range N, b t * p ^ t < p ^ t :=
      lt_of_lt_of_le (by omega) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod] at hd
    split_ifs with h
    · rw [if_pos h] at hd; rw [← hd, Nat.cast_zero]
    · rfl

omit [Fact p.Prime] in
lemma carryI_eq (k l : ℕ) (hp : 1 ≤ p) :
    carryI p k l = ∑ t ∈ range (k + l), (if k ≤ t then p - 1 else 0) * p ^ t := by
  unfold carryI
  induction l with
  | zero =>
    simp only [pow_zero, Nat.sub_self, zero_mul, add_zero]
    exact (Finset.sum_eq_zero fun t ht => by rw [if_neg (by have := mem_range.mp ht; omega), zero_mul]).symm
  | succ l ih =>
    rw [← add_assoc, Finset.sum_range_succ, ← ih, if_pos (by omega)]
    have h1 : 1 ≤ p ^ l := Nat.one_le_pow _ _ hp
    have h2 : 1 ≤ p ^ (l + 1) := Nat.one_le_pow _ _ hp
    zify [h1, h2, hp]
    ring

omit [Fact p.Prime] in
lemma carryJ_eq (k l : ℕ) :
    carryJ p k l = ∑ t ∈ range (k + l + 1), (if t = k + l then 1 else 0) * p ^ t := by
  unfold carryJ
  rw [Finset.sum_range_succ, if_pos rfl, one_mul,
    Finset.sum_eq_zero fun t ht => by rw [if_neg (by have := mem_range.mp ht; omega), zero_mul], zero_add]

lemma idxPolyP_carryJ (k l : ℕ) : idxPolyP p (carryJ p k l) = X ^ (k + l) := by
  have hp2 := (Fact.out : p.Prime).two_le
  rw [carryJ_eq, idxPolyP_of_digits _ _ (fun t => by split_ifs <;> omega), Finset.sum_range_succ, if_pos rfl,
    Finset.sum_eq_zero fun t ht => by rw [if_neg (by have := mem_range.mp ht; omega)]; simp]
  simp

lemma idxPolyP_carryI (k l : ℕ) : idxPolyP p (carryI p k l) = -∑ t ∈ range l, (X : (ZMod p)[X]) ^ (k + t) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hneg : C ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
    rw [← C_1, ← map_add, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega), ZMod.natCast_self, map_zero]
  rw [carryI_eq k l (by omega), idxPolyP_of_digits _ _ (fun t => by split_ifs <;> omega), Finset.sum_range_add,
    Finset.sum_eq_zero fun t ht => by rw [if_neg (by have := mem_range.mp ht; omega)]; simp, zero_add,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [if_pos (by omega)]
  linear_combination (X : (ZMod p)[X]) ^ (k + t) * hneg

/-- **The index difference** of the carry pair: `V_j - V_i = z^k (1 + z + ⋯ + z^ℓ)`. -/
theorem idxPolyP_carry_diff (k l : ℕ) :
    idxPolyP p (carryJ p k l) - idxPolyP p (carryI p k l) = X ^ k * ∑ t ∈ range (l + 1), (X : (ZMod p)[X]) ^ t := by
  rw [idxPolyP_carryJ, idxPolyP_carryI, sub_neg_eq_add, Finset.sum_range_succ, mul_add, Finset.mul_sum, pow_add,
    add_comm]
  simp only [pow_add]

end Poly

section Frame

variable {F : Type*} [Field F] {s : ℕ}

/-- A frame row reads Taylor coefficients: digit `n` of coordinate `c` of `scrGen a L` at `V` is
`∑_{j ≤ n} L_c[n][j] [(z - a_c)^j] V`. -/
lemma genY_scrGen (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (V : F[X]) (n : ℕ) :
    genY (scrGen a L) c V n = ∑ j ∈ range (n + 1), L c n j * (taylor (a c) V).coeff j := by
  have h := genY_comb (fun j k => pas (a c) j k) (L c) V n
  unfold genY scrGen
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pas_sum]

/-- If `(z - a_c)^d ∣ V`, the first `d` digits of coordinate `c` of `V` vanish (lower-triangular `L_c`). -/
lemma genY_scrGen_vanish (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (V : F[X]) (d n : ℕ)
    (hdvd : (X - C (a c)) ^ d ∣ V) (hn : n < d) : genY (scrGen a L) c V n = 0 := by
  rw [genY_scrGen]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [(X_sub_C_pow_dvd_iff (a c) d V).mp hdvd j (by have := mem_range.mp hj; omega), mul_zero]

end Frame

section Torus

lemma torCoord_sq_le {x y B : ℝ} (h : |x - y| ≤ B) (hB : B ≤ 1) : Z3NetDGS.torCoord x y ^ 2 ≤ B ^ 2 := by
  unfold Z3NetDGS.torCoord
  have h0 : 0 ≤ min |x - y| (1 - |x - y|) := le_min (abs_nonneg _) (by linarith)
  exact pow_le_pow_left₀ h0 ((min_le_left _ _).trans h) 2

lemma torDist2_sq {d : ℕ} (x y : Fin d → ℝ) :
    Z3NetDGS.torDist2 x y ^ 2 = ∑ j, Z3NetDGS.torCoord (x j) (y j) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `δ` of the first `N` points is at most the distance of any two of them with different positions, and `≥ 0`. -/
lemma liftDelta_le_pair {d : ℕ} (pt : ℕ → Fin d → ℝ) {N i j : ℕ} (hi : i < N) (hj : j < N) (hne : pt i ≠ pt j) :
    0 ≤ liftDelta pt N ∧ liftDelta pt N ≤ Z3NetDGS.torDist2 (pt i) (pt j) := by
  unfold liftDelta Z3NetDGS.sepRad
  set S := {xy : (Fin d → ℝ) × (Fin d → ℝ) // xy.1 ∈ prefixSet N pt ∧ xy.2 ∈ prefixSet N pt ∧ xy.1 ≠ xy.2}
  have hmem : ∀ x, x < N → pt x ∈ prefixSet N pt := fun x hx => mem_image_of_mem pt (mem_range.mpr hx)
  let e : S := ⟨(pt i, pt j), hmem i hi, hmem j hj, hne⟩
  have hbdd : BddBelow (Set.range fun xy : S => Z3NetDGS.torDist2 xy.1.1 xy.1.2 / 2) :=
    ⟨0, by rintro _ ⟨xy, rfl⟩; exact div_nonneg (Real.sqrt_nonneg _) zero_le_two⟩
  have : Nonempty S := ⟨e⟩
  refine ⟨mul_nonneg zero_le_two (le_ciInf fun xy => div_nonneg (Real.sqrt_nonneg _) zero_le_two), ?_⟩
  have h := ciInf_le hbdd e
  simp only [e] at h
  linarith

end Torus

section Lift

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- The lift of the sequence shifted by `0` is the lift of the sequence. -/
lemma liftPtSh_zero (C : Gen s (ZMod p)) (m : ℕ) :
    liftPtSh (zcode p) C (fun _ _ => 0) m = liftPt (zcode p) C m := by
  funext v c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp [liftPtSh, liftPt]
  · simp [liftPtSh, liftPt, shPoint, shDigit, seqPoint, seqCoord]

/-- **The carry pair of `prop:liftcarry`**: for places `a_c = 0` or `a_c^n = 1` (`n ≥ 1`), `ℓ = n p^r - 1` and
`k + n p^r ≤ m`, the indices `i = (p^ℓ - 1) p^k` and `j = p^{k+ℓ} = i + p^k` are `< p^m`, and the lifted points
(of the sequence shifted by any `ς`) satisfy `‖ŷ_i - ŷ_j‖_T² ≤ (p^k/p^m)² + ∑_c p^{-2 ord(a_c)}` with `ord(0) = k`,
`ord(1) = p^r - 1`, `ord(ζ) = p^r` otherwise (`liftOrd`). -/
theorem liftcarry_pair (a : Fin s → ZMod p) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p)
    (n r k m : ℕ) (hn : 1 ≤ n) (hA : ∀ c, a c = 0 ∨ a c ^ n = 1) (hm : k + n * p ^ r ≤ m) :
    carryI p k (n * p ^ r - 1) < p ^ m ∧ carryJ p k (n * p ^ r - 1) < p ^ m ∧
      carryJ p k (n * p ^ r - 1) = carryI p k (n * p ^ r - 1) + p ^ k ∧
      Z3NetDGS.torDist2 (liftPtSh (zcode p) (scrGen a L) ς m (carryI p k (n * p ^ r - 1)))
          (liftPtSh (zcode p) (scrGen a L) ς m (carryJ p k (n * p ^ r - 1))) ^ 2 ≤
        ((p : ℝ) ^ k / (p : ℝ) ^ m) ^ 2 + ∑ c, (1 / (p : ℝ) ^ liftOrd p r k (a c)) ^ 2 := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  have hnpr : 1 ≤ n * p ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set l := n * p ^ r - 1 with hl
  set i := carryI p k l
  set j := carryJ p k l
  have hpl : 1 ≤ p ^ l := Nat.one_le_pow _ _ (by omega)
  have hji : j = i + p ^ k := by
    show p ^ (k + l) = (p ^ l - 1) * p ^ k + p ^ k
    rw [pow_add]; zify [hpl]; ring
  have hj : j < p ^ m := Nat.pow_lt_pow_right (by omega) (by omega)
  refine ⟨by omega, hj, hji, ?_⟩
  -- the index difference and its vanishing
  set H := ∑ t ∈ range n, (X : (ZMod p)[X]) ^ t
  have hD : idxPolyP p j - idxPolyP p i = X ^ k * ((X - 1) ^ (p ^ r - 1) * H ^ (p ^ r)) := by
    rw [idxPolyP_carry_diff, show l + 1 = n * p ^ r by omega, liftD_identity]
  have hdig : ∀ c t, t < liftOrd p r k (a c) →
      shDigit (zcode p) (scrGen a L) ς j c t = shDigit (zcode p) (scrGen a L) ς i c t := by
    intro c t ht
    unfold shDigit
    rw [← genY_idx, ← genY_idx, show idxPolyP p j = (idxPolyP p j - idxPolyP p i) + idxPolyP p i by ring,
      genY_lin, hD, genY_scrGen_vanish a L c _ _ t (liftD_dvd n r k (a c) (hA c)) ht, zero_add]
  have hcoord : ∀ c, |shPoint (zcode p) (scrGen a L) ς i c - shPoint (zcode p) (scrGen a L) ς j c| ≤
      1 / (p : ℝ) ^ liftOrd p r k (a c) := by
    intro c
    exact real_prefix hp2 (fun t => ((zcode p).enc (shDigit (zcode p) (scrGen a L) ς i c t) : ℕ))
      (fun t => ((zcode p).enc (shDigit (zcode p) (scrGen a L) ς j c t) : ℕ)) (fun _ => Fin.isLt _)
      (fun _ => Fin.isLt _) _ (fun t ht => by rw [hdig c t ht])
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hidx : |(i : ℝ) / (p : ℝ) ^ m - (j : ℝ) / (p : ℝ) ^ m| = (p : ℝ) ^ k / (p : ℝ) ^ m := by
    rw [hji, Nat.cast_add, Nat.cast_pow, ← sub_div, show (i : ℝ) - (i + (p : ℝ) ^ k) = -(p : ℝ) ^ k by ring,
      neg_div, abs_neg, abs_of_nonneg (by positivity)]
  have hkm : (p : ℝ) ^ k / (p : ℝ) ^ m ≤ 1 := by
    rw [div_le_one (by positivity)]; exact pow_le_pow_right₀ hp1 (by omega)
  rw [torDist2_sq, Fin.sum_univ_succ]
  simp only [liftPtSh, Fin.cons_zero, Fin.cons_succ]
  refine add_le_add (torCoord_sq_le (le_of_eq hidx) hkm) (Finset.sum_le_sum fun c _ => ?_)
  exact torCoord_sq_le (hcoord c) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ hp1)

/-- **`prop:liftcarry`, sharp form** (any lower-triangular `L_c`, any digital shift, places `0` or `n`-th roots of
unity, not necessarily distinct): `δ(P̂_m)² ≤ (p^k/p^m)² + ∑_c p^{-2 ord(a_c)}`. -/
theorem liftcarry_sharp (a : Fin s → ZMod p) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p)
    (n r k m : ℕ) (hn : 1 ≤ n) (hA : ∀ c, a c = 0 ∨ a c ^ n = 1) (hm : k + n * p ^ r ≤ m) :
    0 ≤ liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) ∧
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) ^ 2 ≤
      ((p : ℝ) ^ k / (p : ℝ) ^ m) ^ 2 + ∑ c, (1 / (p : ℝ) ^ liftOrd p r k (a c)) ^ 2 := by
  obtain ⟨hi, hj, hji, hb⟩ := liftcarry_pair a L ς n r k m hn hA hm
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hne : liftPtSh (zcode p) (scrGen a L) ς m (carryI p k (n * p ^ r - 1)) ≠
      liftPtSh (zcode p) (scrGen a L) ς m (carryJ p k (n * p ^ r - 1)) := by
    intro h
    have h0 := congrFun h 0
    simp only [liftPtSh, Fin.cons_zero] at h0
    rw [div_left_inj' (by positivity)] at h0
    have := pow_pos hp0 k
    exact absurd (by exact_mod_cast h0 : carryI p k (n * p ^ r - 1) = carryJ p k (n * p ^ r - 1)) (by omega)
  obtain ⟨h0, hle⟩ := liftDelta_le_pair _ hi hj hne
  exact ⟨h0, (pow_le_pow_left₀ h0 hle 2).trans hb⟩

/-- **`prop:liftcarry`** (as stated in the paper): a scrambled frame `C_c = L_c P_{a_c}` over `ℤ/pℤ` with distinct
places `A = {a_c} ⊆ {0} ∪ μ_n` (`n ≥ 1`), `k + n p^r ≤ m`, any digital shift:
`δ(P̂_m)² ≤ p^{2(k-m)} + [0 ∈ A] p^{-2k} + |A ∖ {0}| p^{-2(p^r-1)}`. (Neither `n ∣ p-1`, `r ≥ 1`, `k ≥ 1` nor the
nonsingularity of `L_c` is needed.) -/
theorem liftcarry (a : Fin s → ZMod p) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → ZMod p)
    (ς : Fin s → ℕ → ZMod p) (n r k m : ℕ) (hn : 1 ≤ n) (hA : ∀ c, a c = 0 ∨ a c ^ n = 1)
    (hm : k + n * p ^ r ≤ m) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) ^ 2 ≤
      ((p : ℝ) ^ k / (p : ℝ) ^ m) ^ 2 + (if (0 : ZMod p) ∈ univ.image a then 1 else 0) * (1 / (p : ℝ) ^ k) ^ 2 +
        (((univ.image a).erase 0).card : ℝ) * (1 / (p : ℝ) ^ (p ^ r - 1)) ^ 2 := by
  classical
  have hsharp := (liftcarry_sharp a L ς n r k m hn hA hm).2
  suffices hS : ∑ c, (1 / (p : ℝ) ^ liftOrd p r k (a c)) ^ 2 ≤
      (if (0 : ZMod p) ∈ univ.image a then 1 else 0) * (1 / (p : ℝ) ^ k) ^ 2 +
        (((univ.image a).erase 0).card : ℝ) * (1 / (p : ℝ) ^ (p ^ r - 1)) ^ 2 by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hterm : ∀ c, (1 / (p : ℝ) ^ liftOrd p r k (a c)) ^ 2 ≤
      if a c = 0 then (1 / (p : ℝ) ^ k) ^ 2 else (1 / (p : ℝ) ^ (p ^ r - 1)) ^ 2 := by
    intro c
    unfold liftOrd
    split_ifs with h0 h1
    · exact le_rfl
    · exact le_rfl
    · have hpos : (0 : ℝ) < (p : ℝ) ^ (p ^ r - 1) := by positivity
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact one_div_le_one_div_of_le hpos (pow_le_pow_right₀ hp1 (by omega))
  refine (Finset.sum_le_sum fun c _ => hterm c).trans (le_of_eq ?_)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have himg : (univ.filter fun c => ¬ a c = 0).image a = (univ.image a).erase 0 := by
    ext x; simp only [mem_image, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨hc, c, rfl⟩
    · rintro ⟨hx, c, rfl⟩; exact ⟨c, hx, rfl⟩
  have hcard1 : ((univ.filter fun c => ¬ a c = 0).card : ℝ) = (((univ.image a).erase 0).card : ℝ) := by
    rw [← himg, card_image_of_injective _ ha]
  have hcard0 : ((univ.filter fun c => a c = 0).card : ℝ) = if (0 : ZMod p) ∈ univ.image a then 1 else 0 := by
    have himg0 : (univ.filter fun c => a c = 0).image a = (univ.image a).filter fun x => x = 0 := by
      ext x; simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, rfl⟩, hc⟩
      · rintro ⟨⟨c, rfl⟩, hx⟩; exact ⟨c, hx, rfl⟩
    rw [← card_image_of_injective _ ha, himg0, Finset.filter_eq']
    split_ifs <;> simp
  rw [hcard1, hcard0]

/-- One term of the closed forms: with `u = p^{p^r}`, `p^{-2 ord(a)} u² = 1 + [a = 1](p² - 1)` whenever `a ≠ 0` or
`k = p^r`. -/
lemma ord_term (r k : ℕ) (a : ZMod p) (hk : a = 0 → k = p ^ r) :
    (1 / (p : ℝ) ^ liftOrd p r k a) ^ 2 * ((p : ℝ) ^ (p ^ r)) ^ 2 = 1 + if a = 1 then (p : ℝ) ^ 2 - 1 else 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  unfold liftOrd
  by_cases h0 : a = 0
  · rw [if_pos h0, hk h0, if_neg (by rw [h0]; exact zero_ne_one)]
    field_simp; ring
  · rw [if_neg h0]
    by_cases h1 : a = 1
    · rw [if_pos h1, if_pos h1]
      have e : (p : ℝ) ^ (p ^ r) = (p : ℝ) ^ (p ^ r - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hpr]
      rw [e]; field_simp; ring
    · rw [if_neg h1, if_neg h1]; field_simp; ring

/-- `∑_c (1 + [a_c = 1](p² - 1)) ≤ s + p² - 1` for distinct places. -/
lemma sum_ord_le (a : Fin s → ZMod p) (ha : Function.Injective a) :
    ∑ c, (1 + if a c = 1 then (p : ℝ) ^ 2 - 1 else 0) ≤ s + (p : ℝ) ^ 2 - 1 := by
  classical
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp2 : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
  rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (univ.filter fun c => a c = 1).card ≤ 1 :=
    Finset.card_le_one.mpr fun x hx y hy => ha (by rw [(mem_filter.mp hx).2, (mem_filter.mp hy).2])
  have hc' : ((univ.filter fun c => a c = 1).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

/-- **Closed form, places in `{0} ∪ μ_{s-1}`** (`prop:liftcarry`, first case; `s ≥ 2`, distinct places): at
`m = s p^r`, `δ(P̂_m) · p^{p^r} ≤ √(s + p²)`, i.e. `δ(P̂_m) ≤ √(s+p²) N^{-1/s}`. -/
theorem liftcarry_closed0 (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) * (p : ℝ) ^ (p ^ r) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  obtain ⟨h0, hb⟩ := liftcarry_sharp a L ς (s - 1) r (p ^ r) (s * p ^ r) (by omega) hA
    (le_of_eq (by rw [← one_add_mul]; congr 1; omega))
  set u : ℝ := (p : ℝ) ^ (p ^ r)
  have hu1 : 1 ≤ u := one_le_pow₀ hp1
  have hm : (p : ℝ) ^ (s * p ^ r) = u ^ s := by rw [mul_comm, pow_mul]
  have hfirst : ((p : ℝ) ^ (p ^ r) / (p : ℝ) ^ (s * p ^ r)) ^ 2 * u ^ 2 ≤ 1 := by
    rw [hm]
    have hus : u ^ 2 ≤ u ^ s := pow_le_pow_right₀ hu1 hs
    have hpos : 0 < u ^ s := by positivity
    rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
    have : u ^ 2 * u ^ 2 ≤ u ^ s * u ^ s := mul_le_mul hus hus (by positivity) hpos.le
    calc u ^ 2 * u ^ 2 ≤ u ^ s * u ^ s := this
      _ = (u ^ s) ^ 2 := by ring
  have hsum : (∑ c, (1 / (p : ℝ) ^ liftOrd p r (p ^ r) (a c)) ^ 2) * u ^ 2 ≤ s + (p : ℝ) ^ 2 - 1 := by
    rw [Finset.sum_mul]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ord_term r (p ^ r) (a c) (fun _ => rfl)))
      (sum_ord_le a ha)
  rw [← Real.sqrt_sq (mul_nonneg h0 (by positivity : (0 : ℝ) ≤ u))]
  apply Real.sqrt_le_sqrt
  rw [mul_pow]
  nlinarith [hb, hfirst, hsum]

/-- **Closed form, places in `μ_s`** (`prop:liftcarry`, second case; distinct places): at `m = s p^r`,
`δ(P̂_m) · p^{p^r} ≤ √(s + p²)`. -/
theorem liftcarry_closedMu (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) * (p : ℝ) ^ (p ^ r) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hne : ∀ c, a c ≠ 0 := fun c h => by
    have := hA c; rw [h, zero_pow (by omega)] at this; exact zero_ne_one this
  obtain ⟨h0, hb⟩ := liftcarry_sharp a L ς s r 0 (s * p ^ r) hs (fun c => Or.inr (hA c)) (by omega)
  set u : ℝ := (p : ℝ) ^ (p ^ r)
  have hu1 : 1 ≤ u := one_le_pow₀ hp1
  have hm : (p : ℝ) ^ (s * p ^ r) = u ^ s := by rw [mul_comm, pow_mul]
  have hfirst : ((p : ℝ) ^ 0 / (p : ℝ) ^ (s * p ^ r)) ^ 2 * u ^ 2 ≤ 1 := by
    rw [hm, pow_zero]
    have hus : u ≤ u ^ s := le_self_pow₀ hu1 (by omega)
    have hpos : 0 < u ^ s := by positivity
    rw [div_pow, one_pow, one_div_mul_eq_div, div_le_one (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hus 2
  have hsum : (∑ c, (1 / (p : ℝ) ^ liftOrd p r 0 (a c)) ^ 2) * u ^ 2 ≤ s + (p : ℝ) ^ 2 - 1 := by
    rw [Finset.sum_mul]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      ord_term r 0 (a c) (fun h => absurd h (hne c)))) (sum_ord_le a ha)
  rw [← Real.sqrt_sq (mul_nonneg h0 (by positivity : (0 : ℝ) ≤ u))]
  apply Real.sqrt_le_sqrt
  rw [mul_pow]
  nlinarith [hb, hfirst, hsum]

/-- The normalization: `x · p^{p^r} ≤ γ` gives `x · (p^{s p^r})^{1/(s+1)} ≤ γ p^{-p^r/(s+1)}`. -/
lemma norm_of_mul (r : ℕ) (x γ : ℝ) (h : x * (p : ℝ) ^ (p ^ r) ≤ γ) :
    x * ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤ γ * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have e1 : ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) =
      (p : ℝ) ^ (((s * p ^ r : ℕ) : ℝ) * (1 / ((s : ℝ) + 1))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  have e2 : (p : ℝ) ^ (p ^ r) = (p : ℝ) ^ (((p ^ r : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
  have e3 : (p : ℝ) ^ (((s * p ^ r : ℕ) : ℝ) * (1 / ((s : ℝ) + 1))) =
      (p : ℝ) ^ (((p ^ r : ℕ) : ℝ)) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
    rw [← Real.rpow_add hp0]
    congr 1
    push_cast
    field_simp
    ring
  rw [e1, e3, ← mul_assoc, ← e2]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hp0.le _)

/-- **`prop:liftcarry`, normalized, places in `{0} ∪ μ_{s-1}`**: `δ(P̂_m) N^{1/(s+1)} ≤ √(s+p²) p^{-p^r/(s+1)}` at
`m = s p^r`. -/
theorem liftcarry_closed0_norm (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
  norm_of_mul r _ _ (liftcarry_closed0 hs a ha hA L ς r)

/-- **`prop:liftcarry`, normalized, places in `μ_s`**: `δ(P̂_m) N^{1/(s+1)} ≤ √(s+p²) p^{-p^r/(s+1)}`. -/
theorem liftcarry_closedMu_norm (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (s + (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
  norm_of_mul r _ _ (liftcarry_closedMu hs a ha hA L ς r)

/-- **`prop:liftcarry`, the paper's constant for `A ⊆ {0} ∪ μ_{s-1}`**: `γ = √(2 + (s-1)p²)`. -/
theorem liftcarry_gamma0 (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (2 + ((s : ℝ) - 1) * (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  refine (liftcarry_closed0_norm hs a ha hA L ς r).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hpp : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ hp1
  nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hpp)]

/-- **`prop:liftcarry`, the paper's constant for `A ⊆ μ_s`** (as corrected by the audit): `γ = √(1 + s p²)`. -/
theorem liftcarry_gammaMu (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p) (ς : Fin s → ℕ → ZMod p) (r : ℕ) :
    liftDelta (liftPtSh (zcode p) (scrGen a L) ς (s * p ^ r)) (p ^ (s * p ^ r)) *
        ((p : ℝ) ^ (s * p ^ r)) ^ (1 / ((s : ℝ) + 1)) ≤
      Real.sqrt (1 + (s : ℝ) * (p : ℝ) ^ 2) * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
  refine (liftcarry_closedMu_norm hs a ha hA L ς r).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpp : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ hp1
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hpp)]

/-- `γ p^{-p^r/(s+1)} < ε` for some `r`. -/
lemma exists_r_small (γ ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, γ * (p : ℝ) ^ (-(((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))) < ε := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  obtain ⟨r, hr⟩ := exists_nat_gt ((max γ 1 / ε) ^ (s + 1))
  refine ⟨r, ?_⟩
  set y := (p : ℝ) ^ (((p ^ r : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hy0 : 0 < y := Real.rpow_pos_of_pos hp0 _
  have hys : y ^ (s + 1) = (p : ℝ) ^ (p ^ r) := by
    rw [← Real.rpow_natCast y, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast]
    congr 1; push_cast; field_simp
  have hpr : (r : ℝ) ≤ (p : ℝ) ^ (p ^ r) := by
    have h1 : r < p ^ r := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have h2 : (p ^ r : ℕ) ≤ p ^ (p ^ r) := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    exact_mod_cast (h1.le.trans h2)
  have hgt : max γ 1 / ε < y := by
    by_contra h
    push_neg at h
    have := pow_le_pow_left₀ hy0.le h (s + 1)
    linarith
  rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
  calc γ / y ≤ max γ 1 / y := div_le_div_of_nonneg_right (le_max_left _ _) hy0.le
    _ < ε := by
      rw [div_lt_iff₀ hy0]
      rw [div_lt_iff₀ hε] at hgt
      linarith [mul_comm y ε]

/-- **The lifts are not well separated** (`prop:liftcarry`, last sentence): for distinct places in `{0} ∪ μ_{s-1}`
(`s ≥ 2`) or in `μ_s`, every lower-triangular scramble and every digital shift,
`inf_m δ(P̂_m) N^{1/(s+1)} = 0` (`N = p^m`). -/
theorem lift_not_wellsep (hs : 1 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (hA : (2 ≤ s ∧ ∀ c, a c = 0 ∨ a c ^ (s - 1) = 1) ∨ ∀ c, a c ^ s = 1) (L : Fin s → ℕ → ℕ → ZMod p)
    (ς : Fin s → ℕ → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((s : ℝ) + 1)) < ε := by
  obtain ⟨r, hr⟩ := exists_r_small (s := s) (p := p) (Real.sqrt (s + (p : ℝ) ^ 2)) ε hε
  refine ⟨s * p ^ r, lt_of_le_of_lt ?_ hr⟩
  rcases hA with ⟨hs2, hA⟩ | hA
  · exact liftcarry_closed0_norm hs2 a ha hA L ς r
  · exact liftcarry_closedMu_norm hs a ha hA L ς r

/-- **Places `{0, 1}`** (`s = 2`; every two-dimensional sequence of the paper with these places): the lifts are not
well separated, for every lower-triangular scramble and every digital shift. -/
theorem lift01_not_wellsep (a : Fin 2 → ZMod p) (ha : Function.Injective a) (hA : ∀ c, a c = 0 ∨ a c = 1)
    (L : Fin 2 → ℕ → ℕ → ZMod p) (ς : Fin 2 → ℕ → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPtSh (zcode p) (scrGen a L) ς m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((2 : ℕ) + 1 : ℝ)) < ε :=
  lift_not_wellsep (by norm_num) a ha (Or.inl ⟨le_rfl, fun c => by simpa using hA c⟩) L ς ε hε

/-- The residue sequence `𝓡_v` (`def:residue`) with the places `0, 1`: its lifts are not well separated. -/
theorem lift_resSeq01_not_wellsep (a : Fin 2 → ZMod p) (ha : Function.Injective a) (hA : ∀ c, a c = 0 ∨ a c = 1)
    (θ : ZMod p) (v : Fin 2 → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPt (zcode p) (resSeq a θ v) m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((2 : ℕ) + 1 : ℝ)) < ε := by
  obtain ⟨m, hm⟩ := lift01_not_wellsep a ha hA (resL a θ v) (fun _ _ => 0) ε hε
  refine ⟨m, ?_⟩
  rwa [liftPtSh_zero] at hm

/-- The staggered residue sequence `𝓡^⋆_v` (`def:residuestar`, e.g. the brick wall) with the places `0, 1`: its lifts
are not well separated. -/
theorem lift_resStar01_not_wellsep (a : Fin 2 → ZMod p) (ha : Function.Injective a) (hA : ∀ c, a c = 0 ∨ a c = 1)
    (θ : ZMod p) (cs : Fin 2) (μs : ZMod p) (k : Fin 2 → ZMod p) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, liftDelta (liftPt (zcode p) (resStar a θ cs μs k) m) (p ^ m) *
      ((p : ℝ) ^ m) ^ (1 / ((2 : ℕ) + 1 : ℝ)) < ε := by
  obtain ⟨m, hm⟩ := lift01_not_wellsep a ha hA (resStarL a θ cs μs k) (fun _ _ => 0) ε hε
  refine ⟨m, ?_⟩
  rwa [liftPtSh_zero] at hm

end Lift

end GeoSeq
