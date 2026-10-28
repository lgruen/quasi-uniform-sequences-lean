/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Seq
public import GeoSeq.V9Prefix

@[expose] public section

/-!
# GeoSeq stage V9-2 (part 3): `thm:residue`

Prime base `p`, digits in `ℤ/pℤ` read by `zcode`, places `a` distinct, `θ ≠ 0`, check vector
`v ∈ (𝔽_p^*)^s`, `s ≥ 2`, level `K ≥ 1`, prefix `P_{sK-1}` (indices `x < p^{sK-1}`). The fine cell of a
point is `n̂_c = cellIdx x c K` (its first `K` digits in every coordinate).

* `residue_cells` (**`thm:residue`(i)**): the fine cells occupied by the points of `P_{sK-1}` are exactly
  the elements of `Λ_v ∩ [0, p^K)^s`, each holding one point (image = lattice box, injective).
  Proof as in the paper: `n̂_c ≡ y_{c,K-1} (mod p)` and the skeleton relation give `n̂ ∈ Λ_v`; the fine
  cell determines the box of depths `(K-1, K, …, K)` (`(0,s)` property), so distinct points have
  distinct fine cells. Surjectivity: instead of the paper's count, the point in the box of depths
  `(K-1, K, …, K)` named by `n ∈ Λ_v` has fine cell `n` (both are in `Λ_v` and `v_{c_0} ≠ 0` fix the last
  digit of coordinate `c_0`).
* `residue_sep` (**`thm:residue`(ii)**): if `L ≤ ‖(|b| - 𝟏)_+‖_2` for every `0 ≠ b ∈ Λ_v`, then any two
  distinct points of `P_{sK-1}` are at toroidal distance `≥ L p^{-K}`; `residue_sep_ljit` (with
  `L = ℓ_jit(Λ_v)`), `residue_sepAtPrefix` (the paper's form `sep(P_{sK-1}) ≥ p^{-1/s} L`).
-/

namespace GeoSeq

open Finset Polynomial

/-! ## Cell indices -/

section Cells
variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

lemma cellIdx_succ (D : DigitCode R q) (C : Gen s R) (x : ℕ) (c : Fin s) (K : ℕ) :
    cellIdx D C x c (K + 1) = cellIdx D C x c K * q + (D.enc (seqDigit D C x c K) : ℕ) := by
  unfold cellIdx
  rw [Fin.sum_univ_castSucc, Finset.sum_mul]
  simp only [Fin.coe_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn := n.isLt
  rw [mul_assoc, ← pow_succ]
  congr 2
  omega

lemma cellIdx_zero (D : DigitCode R q) (C : Gen s R) (x : ℕ) (c : Fin s) :
    cellIdx D C x c 0 = 0 := by
  simp [cellIdx]

lemma cellIdx_lt (D : DigitCode R q) (C : Gen s R) (x : ℕ) (c : Fin s) (K : ℕ) :
    cellIdx D C x c K < q ^ K := by
  induction K with
  | zero => simp [cellIdx_zero]
  | succ K ih =>
    rw [cellIdx_succ, pow_succ]
    have he := (D.enc (seqDigit D C x c K)).isLt
    calc cellIdx D C x c K * q + (D.enc (seqDigit D C x c K) : ℕ)
        < cellIdx D C x c K * q + q := by omega
      _ = (cellIdx D C x c K + 1) * q := by ring
      _ ≤ q ^ K * q := Nat.mul_le_mul_right _ ih

lemma cellIdx_div (D : DigitCode R q) (C : Gen s R) (x : ℕ) (c : Fin s) (K : ℕ) :
    cellIdx D C x c (K + 1) / q = cellIdx D C x c K := by
  rw [cellIdx_succ, mul_comm, Nat.mul_add_div (NeZero.pos q),
    Nat.div_eq_of_lt (D.enc (seqDigit D C x c K)).isLt, add_zero]

end Cells

lemma cast_cellIdx (p : ℕ) [Fact p.Prime] {s : ℕ} (C : Gen s (ZMod p)) (x : ℕ) (c : Fin s) (K : ℕ) :
    ((cellIdx (zcode p) C x c (K + 1) : ℕ) : ZMod p) = seqDigit (zcode p) C x c K := by
  rw [cellIdx_succ]
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_add]
  exact ZMod.natCast_zmod_val _

/-! ## `thm:residue`(i): occupied fine cells -/

section Thm
variable (p : ℕ) [Fact p.Prime] {s : ℕ}

/-- The depth vector `(K-1, K, …, K)` (`K - 1` in coordinate `c_0`) of a box of volume `p^{-(sK-1)}`. -/
def skelDepth (c0 : Fin s) (K : ℕ) : Fin s → ℕ := fun c => if c = c0 then K - 1 else K

lemma skelDepth_sum (c0 : Fin s) (K : ℕ) (hK : 1 ≤ K) : ∑ c, skelDepth c0 K c = s * K - 1 := by
  have h : ∑ c, skelDepth c0 K c + 1 = s * K := by
    have : ∀ c, skelDepth c0 K c + (if c = c0 then 1 else 0) = K := fun c => by
      unfold skelDepth; split_ifs <;> omega
    calc ∑ c, skelDepth c0 K c + 1
        = ∑ c, skelDepth c0 K c + ∑ c : Fin s, (if c = c0 then 1 else 0) := by
          rw [Finset.sum_ite_eq']; simp
      _ = ∑ c : Fin s, K := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun c _ => this c
      _ = s * K := by simp
  omega

variable {p}

lemma cell_lat (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x : ℕ)
    (hx : x < p ^ (s * K - 1)) :
    InLat v (fun c => (cellIdx (zcode p) (resSeq a θ v) x c K : ℤ)) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have := resSeq_skel_seq (zcode p) a ha θ v hv (K' + 1) hK (by omega) x hx
  unfold InLat
  simp only [Int.cast_natCast, cast_cellIdx]
  simpa using this

lemma cell_inj (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1))
    (h : ∀ c, cellIdx (zcode p) (resSeq a θ v) x c K = cellIdx (zcode p) (resSeq a θ v) y c K) :
    x = y := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set C := resSeq a θ v
  set c0 : Fin s := ⟨0, by omega⟩
  have hseq := resSeq_t0 (zcode p) a ha θ hθ v hv
  obtain ⟨z, -, hz⟩ := hseq (s * (K' + 1) - 1) 0 (skelDepth c0 (K' + 1))
    (skelDepth_sum c0 _ hK) (fun c => cellIdx (zcode p) C x c (skelDepth c0 (K' + 1) c))
    (fun c => cellIdx_lt _ _ _ _ _)
  have hcell : ∀ w, (∀ c, cellIdx (zcode p) C w c (K' + 1) = cellIdx (zcode p) C x c (K' + 1)) →
      ∀ c, cellIdx (zcode p) C w c (skelDepth c0 (K' + 1) c) =
        cellIdx (zcode p) C x c (skelDepth c0 (K' + 1) c) := by
    intro w hw c
    unfold skelDepth
    split_ifs
    · simp only [Nat.add_sub_cancel]
      rw [← cellIdx_div (zcode p) C w c K', ← cellIdx_div (zcode p) C x c K', hw c]
    · exact hw c
  have hxz := hz x ⟨by simp [hx], fun c => rfl⟩
  have hyz := hz y ⟨by simp [hy], hcell y fun c => (h c).symm⟩
  rw [hxz, hyz]

lemma cell_surj (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (n : Fin s → ℕ)
    (hn : ∀ c, n c < p ^ K) (hlat : InLat v (fun c => (n c : ℤ))) :
    ∃ x, x < p ^ (s * K - 1) ∧ ∀ c, cellIdx (zcode p) (resSeq a θ v) x c K = n c := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set C := resSeq a θ v
  set c0 : Fin s := ⟨0, by omega⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hseq := resSeq_t0 (zcode p) a ha θ hθ v hv
  set tgt : Fin s → ℕ := fun c => if c = c0 then n c0 / p else n c
  obtain ⟨x, ⟨⟨-, hxlt⟩, hx⟩, -⟩ := hseq (s * (K' + 1) - 1) 0 (skelDepth c0 (K' + 1))
    (skelDepth_sum c0 _ hK) tgt (by
      intro c
      simp only [tgt, skelDepth]
      split_ifs with hc
      · simp only [Nat.add_sub_cancel]
        rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]; exact hn c0
      · exact hn c)
  rw [zero_add, one_mul] at hxlt
  refine ⟨x, hxlt, ?_⟩
  have hoth : ∀ c, c ≠ c0 → cellIdx (zcode p) C x c (K' + 1) = n c := by
    intro c hc
    have := hx c
    simp only [skelDepth, tgt, if_neg hc] at this
    exact this
  have hdiv : cellIdx (zcode p) C x c0 (K' + 1) / p = n c0 / p := by
    have := hx c0
    simp only [skelDepth, tgt, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [cellIdx_div (zcode p) C x c0 K']
    exact this
  -- the last digit of coordinate `c_0` from the two lattice relations
  have hxl := cell_lat hs a ha θ v hv (K' + 1) hK x hxlt
  unfold InLat at hxl hlat
  rw [← Finset.add_sum_erase _ _ (mem_univ c0)] at hxl hlat
  have hrest : ∑ c ∈ univ.erase c0, v c * (((cellIdx (zcode p) C x c (K' + 1) : ℕ) : ℤ) : ZMod p) =
      ∑ c ∈ univ.erase c0, v c * (((n c : ℕ) : ℤ) : ZMod p) :=
    Finset.sum_congr rfl fun c hc => by rw [hoth c (Finset.ne_of_mem_erase hc)]
  rw [hrest] at hxl
  have hmod : ((cellIdx (zcode p) C x c0 (K' + 1) : ℕ) : ZMod p) = ((n c0 : ℕ) : ZMod p) := by
    have h1 : v c0 * ((((cellIdx (zcode p) C x c0 (K' + 1) : ℕ) : ℤ) : ZMod p) -
        (((n c0 : ℕ) : ℤ) : ZMod p)) = 0 := by
      rw [mul_sub]; linear_combination hxl - hlat
    have h2 := (mul_eq_zero.mp h1).resolve_left (hv c0)
    simpa [sub_eq_zero] using h2
  rw [ZMod.natCast_eq_natCast_iff'] at hmod
  intro c
  by_cases hc : c = c0
  · subst hc
    rw [← Nat.div_add_mod (cellIdx (zcode p) C x c0 (K' + 1)) p, hdiv, hmod, Nat.div_add_mod]
  · exact hoth c hc

/-- **`thm:residue`(i)**: for `K ≥ 1` the fine cells `n̂(x) = (cellIdx x c K)_c` occupied by the points of
`P_{sK-1}` (indices `x < p^{sK-1}`) are exactly the elements of `Λ_v ∩ [0, p^K)^s`, each holding one point. -/
theorem residue_cells (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    (fun x c => cellIdx (zcode p) (resSeq a θ v) x c K) '' Set.Iio (p ^ (s * K - 1)) =
      {n : Fin s → ℕ | (∀ c, n c < p ^ K) ∧ InLat v (fun c => (n c : ℤ))} ∧
    Set.InjOn (fun x c => cellIdx (zcode p) (resSeq a θ v) x c K) (Set.Iio (p ^ (s * K - 1))) := by
  refine ⟨Set.ext fun n => ⟨?_, ?_⟩, fun x hx y hy hxy => ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun c => cellIdx_lt _ _ _ _ _, cell_lat hs a ha θ v hv K hK x hx⟩
  · rintro ⟨hn, hlat⟩
    obtain ⟨x, hx, hxn⟩ := cell_surj hs a ha θ hθ v hv K hK n hn hlat
    exact ⟨x, hx, funext hxn⟩
  · exact cell_inj hs a ha θ hθ v hv K hK x y hx hy fun c => congrFun hxy c

end Thm

/-! ## `thm:residue`(ii): separation -/

/-- The representative of `D` modulo `Q` closest to `0` (for `|D| < Q`): `D`, `D - Q` or `D + Q`. -/
def cenRep (Q : ℕ) (D : ℤ) : ℤ := if 2 * |D| ≤ Q then D else if 0 < D then D - Q else D + Q

lemma cenRep_abs (Q : ℕ) (D : ℤ) (hD : |D| < Q) :
    |cenRep Q D| ≤ |D| ∧ |cenRep Q D| ≤ Q - |D| := by
  unfold cenRep
  split_ifs with h1 h2
  · omega
  · rw [abs_of_pos h2] at h1 hD ⊢; rw [abs_of_neg (by omega)]; omega
  · have h2' : D ≤ 0 := by omega
    rw [abs_of_nonpos h2'] at h1 hD ⊢
    rcases (show D + Q ≥ 0 by omega).lt_or_eq with h | h
    · rw [abs_of_pos h]; omega
    · rw [← h, abs_zero]; omega

lemma cenRep_eq_zero (Q : ℕ) (D : ℤ) (hD : |D| < Q) (h : cenRep Q D = 0) : D = 0 := by
  unfold cenRep at h
  split_ifs at h with h1 h2
  · exact h
  · rw [abs_of_pos h2] at hD; omega
  · rw [abs_of_nonpos (by omega)] at hD; omega

lemma cenRep_modEq (Q : ℕ) (D : ℤ) : ∃ t : ℤ, cenRep Q D = D + t * Q := by
  unfold cenRep
  split_ifs
  · exact ⟨0, by ring⟩
  · exact ⟨-1, by ring⟩
  · exact ⟨1, by ring⟩

/-- One coordinate of `thm:residue`(ii): two points in the closed fine cells `n, m < Q` (side `1/Q`) are at
toroidal distance `≥ (|b| - 1)_+ / Q`, `b` the representative of `m - n` modulo `Q` closest to `0`. -/
lemma torCoord_cell (Q : ℕ) (hQ : 0 < Q) (x y : ℝ) (n m : ℕ) (hn : n < Q) (hm : m < Q)
    (hx : (n : ℝ) ≤ Q * x ∧ Q * x ≤ n + 1) (hy : (m : ℝ) ≤ Q * y ∧ Q * y ≤ m + 1)
    (hx01 : 0 ≤ x ∧ x ≤ 1) (hy01 : 0 ≤ y ∧ y ≤ 1) :
    max (|((cenRep Q ((m : ℤ) - n) : ℤ) : ℝ)| - 1) 0 ≤ Q * Z3NetDGS.torCoord x y := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨hb1, hb2⟩ := cenRep_abs Q ((m : ℤ) - n) (by rw [abs_lt]; omega)
  have hb1' : |((cenRep Q ((m : ℤ) - n) : ℤ) : ℝ)| ≤ |(m : ℝ) - n| := by
    have := (Int.cast_le (R := ℝ)).mpr hb1
    push_cast at this; exact this
  have hb2' : |((cenRep Q ((m : ℤ) - n) : ℤ) : ℝ)| ≤ Q - |(m : ℝ) - n| := by
    have := (Int.cast_le (R := ℝ)).mpr hb2
    push_cast at this; exact this
  unfold Z3NetDGS.torCoord
  have e1 : (Q : ℝ) * |x - y| = |(Q : ℝ) * x - Q * y| := by
    rw [← mul_sub, abs_mul, abs_of_pos hQr]
  rw [mul_min_of_nonneg _ _ hQr.le, mul_sub, mul_one, e1]
  have hxy : |x - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hQxy : |(Q : ℝ) * x - Q * y| ≤ Q := by
    rw [← mul_sub, abs_mul, abs_of_pos hQr]; nlinarith [abs_nonneg (x - y)]
  have hA : |(m : ℝ) - n| - 1 ≤ |(Q : ℝ) * x - Q * y| := by
    rcases abs_cases ((m : ℝ) - n) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases ((Q : ℝ) * x - Q * y) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith
  refine le_min (max_le ?_ (abs_nonneg _)) (max_le ?_ (by linarith))
  · linarith
  · have : |(Q : ℝ) * x - Q * y| ≤ |(m : ℝ) - n| + 1 := by
      rcases abs_cases ((m : ℝ) - n) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
        rcases abs_cases ((Q : ℝ) * x - Q * y) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith
    linarith

section Sep
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

omit [Fact p.Prime] in
lemma ljit_le (v : Fin s → ZMod p) (b : Fin s → ℤ) (hb : b ≠ 0) (hlat : InLat v b) :
    ljit v ≤ jitNorm b := by
  unfold ljit
  have hbdd : BddBelow (Set.range fun b : {b : Fin s → ℤ // b ≠ 0 ∧ InLat v b} => jitNorm b.1) :=
    ⟨0, by rintro _ ⟨b, rfl⟩; exact Real.sqrt_nonneg _⟩
  exact ciInf_le hbdd ⟨b, hb, hlat⟩

/-- `ℓ_jit(Λ_v) ≥ L` as soon as every nonzero lattice vector has `‖(|b| - 𝟏)_+‖_2 ≥ L`. -/
lemma le_ljit (hs : 1 ≤ s) (v : Fin s → ZMod p) (L : ℝ)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) : L ≤ ljit v := by
  unfold ljit
  set c0 : Fin s := ⟨0, by omega⟩
  have hne : Nonempty {b : Fin s → ℤ // b ≠ 0 ∧ InLat v b} := by
    refine ⟨⟨fun c => if c = c0 then (p : ℤ) else 0, fun h => ?_, ?_⟩⟩
    · have := congrFun h c0
      simp only [↓reduceIte, Pi.zero_apply, Nat.cast_eq_zero] at this
      exact (Fact.out : p.Prime).ne_zero this
    · unfold InLat
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases h : c = c0 <;> simp [h]
  exact le_ciInf fun b => hL b.1 b.2.1 b.2.2

lemma seqPoint_cell (C : Gen s (ZMod p)) (x : ℕ) (c : Fin s) (K : ℕ) :
    ((cellIdx (zcode p) C x c K : ℕ) : ℝ) ≤ ((p ^ K : ℕ) : ℝ) * seqPoint (zcode p) C x c ∧
      ((p ^ K : ℕ) : ℝ) * seqPoint (zcode p) C x c ≤ (cellIdx (zcode p) C x c K : ℝ) + 1 := by
  push_cast
  exact coord_cell (Fact.out : p.Prime).two_le (zcode p) C x c K

lemma seqPoint_unit (C : Gen s (ZMod p)) (x : ℕ) (c : Fin s) :
    0 ≤ seqPoint (zcode p) C x c ∧ seqPoint (zcode p) C x c ≤ 1 := by
  have := coord_cell (Fact.out : p.Prime).two_le (zcode p) C x c 0
  simp only [pow_zero, one_mul] at this
  rw [cellIdx_zero] at this
  simpa using this

/-- **`thm:residue`(ii)** (lattice form): if `L ≤ ‖(|b| - 𝟏)_+‖_2` for every nonzero `b ∈ Λ_v`, then any two
distinct points of `P_{sK-1}` have toroidal distance `≥ L · p^{-K}`. -/
theorem residue_sep (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    L ≤ (p : ℝ) ^ K *
      Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq a θ v) x) (seqPoint (zcode p) (resSeq a θ v) y) := by
  set C := resSeq a θ v
  set Q : ℕ := p ^ K with hQdef
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hQ : 0 < Q := pow_pos hp K
  set n : Fin s → ℕ := fun c => cellIdx (zcode p) C x c K
  set m : Fin s → ℕ := fun c => cellIdx (zcode p) C y c K
  set b : Fin s → ℤ := fun c => cenRep Q ((m c : ℤ) - n c)
  have hn : ∀ c, n c < Q := fun c => cellIdx_lt _ _ _ _ _
  have hm : ∀ c, m c < Q := fun c => cellIdx_lt _ _ _ _ _
  have hD : ∀ c, |((m c : ℤ) - n c)| < Q := fun c => by
    have := hn c; have := hm c; rw [abs_lt]; omega
  -- `b ≠ 0`
  have hb0 : b ≠ 0 := by
    intro hb
    apply hxy
    refine cell_inj hs a ha θ hθ v hv K hK x y hx hy fun c => ?_
    have := cenRep_eq_zero Q _ (hD c) (congrFun hb c)
    show n c = m c
    omega
  -- `b ∈ Λ_v`
  have hblat : InLat v b := by
    have hx' : InLat v (fun c => ((n c : ℕ) : ℤ)) := cell_lat hs a ha θ v hv K hK x hx
    have hy' : InLat v (fun c => ((m c : ℕ) : ℤ)) := cell_lat hs a ha θ v hv K hK y hy
    unfold InLat at hx' hy' ⊢
    have hcast : ∀ c, ((b c : ℤ) : ZMod p) = ((m c : ℤ) : ZMod p) - ((n c : ℤ) : ZMod p) := by
      intro c
      obtain ⟨t, ht⟩ := cenRep_modEq Q ((m c : ℤ) - n c)
      show ((cenRep Q ((m c : ℤ) - n c) : ℤ) : ZMod p) = _
      rw [ht]
      push_cast
      rw [hQdef]
      push_cast
      rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
    calc ∑ c, v c * ((b c : ℤ) : ZMod p)
        = ∑ c, (v c * (((m c : ℕ) : ℤ) : ZMod p) - v c * (((n c : ℕ) : ℤ) : ZMod p)) :=
          Finset.sum_congr rfl fun c _ => by rw [hcast c, mul_sub]
      _ = 0 := by
          beta_reduce at hx' hy'
          exact (Finset.sum_sub_distrib _ _).trans ((congrArg₂ (· - ·) hy' hx').trans (sub_zero 0))
  have hLb := hL b hb0 hblat
  -- coordinatewise bound and assembly
  have hcoord : ∀ c, max (|((b c : ℤ) : ℝ)| - 1) 0 ≤
      (Q : ℝ) * Z3NetDGS.torCoord (seqPoint (zcode p) C x c) (seqPoint (zcode p) C y c) :=
    fun c => torCoord_cell Q hQ _ _ (n c) (m c) (hn c) (hm c) (seqPoint_cell C x c K)
      (seqPoint_cell C y c K) (seqPoint_unit C x c) (seqPoint_unit C y c)
  have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  calc L ≤ jitNorm b := hLb
    _ ≤ Real.sqrt (∑ c, ((Q : ℝ) *
          Z3NetDGS.torCoord (seqPoint (zcode p) C x c) (seqPoint (zcode p) C y c)) ^ 2) := by
        unfold jitNorm
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
        exact pow_le_pow_left₀ (le_max_right _ _) (hcoord c) 2
    _ = (p : ℝ) ^ K *
          Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
        unfold Z3NetDGS.torDist2
        simp_rw [mul_pow]
        rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq hQr, hQdef]
        push_cast
        rfl

/-- **`thm:residue`(ii)**: any two distinct points of `P_{sK-1}` have toroidal distance
`≥ ℓ_jit(Λ_v) · p^{-K}`. -/
theorem residue_sep_ljit (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    ljit v ≤ (p : ℝ) ^ K *
      Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq a θ v) x) (seqPoint (zcode p) (resSeq a θ v) y) :=
  residue_sep hs a ha θ hθ v hv (ljit v) (fun b hb hlat => ljit_le v b hb hlat) K hK x y hx hy hxy

omit [Fact p.Prime] in
/-- `p^{-1/s} (p^{sK-1})^{-1/s} = p^{-K}`. -/
lemma prefix_scale (hp : 0 < p) (hs : 1 ≤ s) (K : ℕ) (hK : 1 ≤ K) :
    (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ))) = ((p : ℝ) ^ K)⁻¹ := by
  have hsK : 1 ≤ s * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [← Real.mul_rpow (by positivity) (by positivity), ← pow_succ', Nat.sub_add_cancel hsK,
    mul_comm s K, pow_mul]
  have : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  have := rpow_pow_inv_self (q := p ^ K) (by positivity) hs
  push_cast at this
  exact this

/-- **`thm:residue`(ii)** in the paper's normalization: `sep(P_{sK-1}) ≥ p^{-1/s} L` for every `K ≥ 1`. -/
theorem residue_sepAtPrefix (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) (resSeq a θ v))
      ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  intro x y hx hy hxy
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := residue_sep hs a ha θ hθ v hv L hL K hK x y hx hy hxy
  have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  calc (p : ℝ) ^ (-(1 / (s : ℝ))) * L * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))
      = L * ((p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))) := by ring
    _ = L / (p : ℝ) ^ K := by rw [prefix_scale hp (by omega) K hK, div_eq_mul_inv]
    _ ≤ _ := by rw [div_le_iff₀ hpK]; linarith

end Sep

end GeoSeq
