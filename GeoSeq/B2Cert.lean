/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B2Law
public import GeoSeq.Cert
public import GeoSeq.Fidelity
public import GeoSeq.Mesh

@[expose] public section

/-!
# GeoSeq stage S5: the finite certificate of `thm:B2`

* Lower bounds for `f_j` in base `2` (`gapNum (zcode 2) j`): `|enc(R ⊕ σ) − enc(R)| ≤ enc(σ)` gives
  `gapNum(±1, σ) ≥ 2^j − 1 − enc σ`; the leading digit of `σ` gives `gapNum(0, σ) ≥ topGap σ − 1`
  (`topGap σ = 2^{t+1} − enc σ`, `2^t` the leading bit). Both are attained (`f_12` values of the binding
  case below are checked with explicit witnesses).
* The 35 distinct `12`-digit response tuples (`b2TW`, as four 12-bit words `D_i(l)[c][c']`, digit
  `i` = bit `11 − i`) and the map `l ↦ tuple` for `1 ≤ l ≤ 63` (`b2Idx`), checked by kernel `decide`
  against the computable law `b2lawC`.
* The certificate minimum `2269618 = min ∑_c gapNum(e_c, σ_c)²` over the 35² tuple pairs and the step
  patterns (kernel `decide` on integers / bit vectors).
-/

namespace GeoSeq

open Finset

/-! ## Digit vectors in base two -/

variable {R : Type*} [CommRing R] {q : ℕ}

lemma encVec_succ (D : DigitCode R q) {j : ℕ} (r : Fin (j + 1) → R) :
    encVec D r = (D.enc (r 0) : ℕ) * q ^ j + encVec D (Fin.tail r) := by
  unfold encVec
  rw [Fin.sum_univ_succ, show (j + 1 - 1 - ((0 : Fin (j + 1)) : ℕ)) = j by simp]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  simp only [Fin.tail, Fin.val_succ]
  congr 2
  omega

lemma encVec_zero (D : DigitCode R q) (r : Fin 0 → R) : encVec D r = 0 := by
  simp [encVec]

lemma encVec_lt [NeZero q] (D : DigitCode R q) {j : ℕ} (r : Fin j → R) : encVec D r < q ^ j := by
  induction j with
  | zero => simp [encVec_zero]
  | succ j ih =>
    rw [encVec_succ, pow_succ]
    have h1 := ih (Fin.tail r)
    have h2 : (D.enc (r 0) : ℕ) + 1 ≤ q := (D.enc (r 0)).isLt
    nlinarith

/-- The code `zcode 2` reads the value. -/
lemma z2enc (x : ZMod 2) : ((zcode 2).enc x : ℕ) = x.val := rfl

lemma z2_digit_diff (a b : ZMod 2) : |((a + b).val : ℤ) - a.val| = b.val := by
  fin_cases a <;> fin_cases b <;> decide

lemma z2_digit_diff_zero (a : ZMod 2) : ((a + 0).val : ℤ) - a.val = 0 := by
  fin_cases a <;> decide

/-- `|enc(R ⊕ σ) − enc(R)| ≤ enc(σ)` in base two. -/
lemma enc_diff_le {j : ℕ} (r σ : Fin j → ZMod 2) :
    |(encVec (zcode 2) (r + σ) : ℤ) - encVec (zcode 2) r| ≤ encVec (zcode 2) σ := by
  induction j with
  | zero => simp [encVec_zero]
  | succ j ih =>
    rw [encVec_succ, encVec_succ, encVec_succ (zcode 2) σ]
    have ht : Fin.tail (r + σ) = Fin.tail r + Fin.tail σ := rfl
    rw [ht]
    have h0 := z2_digit_diff (r 0) (σ 0)
    have hi := ih (Fin.tail r) (Fin.tail σ)
    simp only [z2enc, Pi.add_apply] at h0 hi ⊢
    push_cast
    have e : ((r 0 + σ 0).val : ℤ) * 2 ^ j + encVec (zcode 2) (Fin.tail r + Fin.tail σ) -
        ((r 0).val * 2 ^ j + encVec (zcode 2) (Fin.tail r)) =
        (((r 0 + σ 0).val : ℤ) - (r 0).val) * 2 ^ j +
          ((encVec (zcode 2) (Fin.tail r + Fin.tail σ) : ℤ) - encVec (zcode 2) (Fin.tail r)) := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, h0, abs_of_pos (by positivity)]
    linarith

/-- The bound for `e = 0`: `2^{t+1} − enc σ` with `2^t` the leading bit of `σ` (`0` for `σ = 0`). -/
def topGap : (j : ℕ) → (Fin j → ZMod 2) → ℕ
  | 0, _ => 0
  | j + 1, σ => if σ 0 = 1 then 2 ^ j - encVec (zcode 2) (Fin.tail σ) else topGap j (Fin.tail σ)

lemma topGap_le {j : ℕ} (r σ : Fin j → ZMod 2) :
    (topGap j σ : ℤ) ≤ |(encVec (zcode 2) (r + σ) : ℤ) - encVec (zcode 2) r| := by
  induction j with
  | zero => simp [topGap]
  | succ j ih =>
    rw [encVec_succ, encVec_succ]
    have ht : Fin.tail (r + σ) = Fin.tail r + Fin.tail σ := rfl
    rw [ht]
    simp only [z2enc, Pi.add_apply]
    push_cast
    have e : ((r 0 + σ 0).val : ℤ) * 2 ^ j + encVec (zcode 2) (Fin.tail r + Fin.tail σ) -
        ((r 0).val * 2 ^ j + encVec (zcode 2) (Fin.tail r)) =
        (((r 0 + σ 0).val : ℤ) - (r 0).val) * 2 ^ j +
          ((encVec (zcode 2) (Fin.tail r + Fin.tail σ) : ℤ) - encVec (zcode 2) (Fin.tail r)) := by
      ring
    rw [e]
    by_cases h1 : σ 0 = 1
    · simp only [topGap, h1, ite_true]
      have hlt := encVec_lt (zcode 2) (Fin.tail σ)
      have hd := z2_digit_diff (r 0) (σ 0)
      rw [h1] at hd
      have hd' : |((r 0 + 1).val : ℤ) - (r 0).val| = 1 := by rw [hd]; rfl
      have hrest := enc_diff_le (Fin.tail r) (Fin.tail σ)
      rw [Nat.cast_sub hlt.le]
      push_cast
      set A := (((r 0 + 1).val : ℤ) - (r 0).val) * 2 ^ j
      set B := (encVec (zcode 2) (Fin.tail r + Fin.tail σ) : ℤ) - encVec (zcode 2) (Fin.tail r)
      have hA : |A| = 2 ^ j := by
        simp only [A]; rw [abs_mul, hd', one_mul, abs_of_pos (by positivity)]
      have h := abs_add_le (A + B) (-B)
      rw [add_neg_cancel_right, abs_neg, hA] at h
      linarith
    · have h0 : σ 0 = 0 := by
        have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
        exact this _ h1
      simp only [topGap, h1, ite_false]
      rw [h0, z2_digit_diff_zero, zero_mul, zero_add]
      exact ih (Fin.tail r) (Fin.tail σ)

lemma gapNum_ge (D : DigitCode R q) [Fintype R] [DecidableEq R] (j : ℕ) (e : ℤ) (σ : Fin j → R)
    (B : ℕ) (hB : ∀ r : Fin j → R,
      B ≤ ((e * (q : ℤ) ^ j + (encVec D (r + σ) : ℤ) - (encVec D r : ℤ)).natAbs)) :
    B - 1 ≤ gapNum D j e σ := by
  unfold gapNum
  apply Nat.sub_le_sub_right
  apply Finset.le_min'
  intro y hy
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hy
  exact hB r

lemma gapNum_le (D : DigitCode R q) [Fintype R] [DecidableEq R] (j : ℕ) (e : ℤ) (σ : Fin j → R)
    (r : Fin j → R) :
    gapNum D j e σ ≤ ((e * (q : ℤ) ^ j + (encVec D (r + σ) : ℤ) - (encVec D r : ℤ)).natAbs) - 1 := by
  unfold gapNum
  apply Nat.sub_le_sub_right
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))

/-- `f_j(±1, σ) ≥ (2^j − 1 − enc σ)/2^j` in base two. -/
lemma gapNum_pm (j : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) (σ : Fin j → ZMod 2) :
    2 ^ j - encVec (zcode 2) σ - 1 ≤ gapNum (zcode 2) j e σ := by
  apply gapNum_ge
  intro r
  have hd := enc_diff_le r σ
  have hlt := encVec_lt (zcode 2) σ
  zify [hlt.le]
  rcases he with rfl | rfl
  · rw [abs_le] at hd
    rw [le_abs]; left; linarith
  · rw [abs_le] at hd
    rw [le_abs]; right; linarith

/-- `f_j(0, σ) ≥ (topGap σ − 1)/2^j` in base two. -/
lemma gapNum_zero2 (j : ℕ) (σ : Fin j → ZMod 2) : topGap j σ - 1 ≤ gapNum (zcode 2) j 0 σ := by
  apply gapNum_ge
  intro r
  have h := topGap_le r σ
  zify
  simpa using h

/-- The certificate lower bound for one coordinate, by the flag `f = |e_c| ∈ {0, 1}`. -/
def gapLB (f : ℕ) (σ : Fin 12 → ZMod 2) : ℕ :=
  (if f = 0 then topGap 12 σ else 2 ^ 12 - encVec (zcode 2) σ) - 1

lemma gapLB_le (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (σ : Fin 12 → ZMod 2) :
    gapLB e.natAbs σ ≤ gapNum (zcode 2) 12 e σ := by
  unfold gapLB
  rcases (show e = -1 ∨ e = 0 ∨ e = 1 by omega) with rfl | rfl | rfl
  · simpa using gapNum_pm 12 (-1) (Or.inr rfl) σ
  · simpa using gapNum_zero2 12 σ
  · simpa using gapNum_pm 12 1 (Or.inl rfl) σ

/-! ## The finite data: 35 response tuples -/

/-- The 35 distinct tuples `(D_i(l))_{i<12}` (`lem:octave`), as words
`[D(l)[0][0], D(l)[0][1], D(l)[1][0], D(l)[1][1]]`, digit `i` = bit `11 − i`. -/
def b2TW : List (List ℕ) :=
  [[3992, 3072, 2592, 0],
    [816, 2968, 1088, 2592],
    [2552, 2216, 672, 3680],
    [1008, 3784, 1345, 1760],
    [2169, 3592, 162, 2017],
    [243, 3977, 325, 1507],
    [3711, 3210, 2218, 487],
    [255, 2700, 341, 2543],
    [3687, 2688, 2186, 2559],
    [207, 2712, 277, 2527],
    [3591, 2728, 2058, 2463],
    [15, 2760, 21, 2335],
    [3975, 2568, 2570, 2079],
    [783, 2952, 1045, 2591],
    [2439, 2184, 522, 3615],
    [783, 3720, 1045, 1567],
    [2439, 3720, 522, 1567],
    [783, 3720, 1044, 1567],
    [2438, 3720, 520, 1566],
    [780, 3721, 1040, 1564],
    [2432, 3722, 512, 1560],
    [768, 3724, 1024, 1552],
    [2456, 3712, 544, 1536],
    [816, 3736, 1088, 1568],
    [2552, 3752, 672, 1632],
    [1008, 3784, 1344, 1760],
    [2168, 3592, 160, 2016],
    [240, 3976, 320, 1504],
    [3704, 3208, 2208, 480],
    [240, 2696, 320, 2528],
    [3704, 2696, 2208, 2528],
    [240, 2696, 321, 2528],
    [3705, 2696, 2210, 2529],
    [243, 2697, 325, 2531],
    [3711, 2698, 2218, 2535]]

/-- `l ↦` index of its tuple in `b2TW`, for `l = 1, …, 63` (list position `l − 1`). -/
def b2Idx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 29, 30, 29, 30, 29, 30, 29, 30, 29, 30, 29, 30, 29, 30, 29, 30, 29, 30, 31, 32, 33, 34, 7, 8, 9, 10, 11, 12, 13, 14]

/-- Word of entry `(c, c')` of tuple `k`. -/
def b2w (k : ℕ) (c c' : Fin 2) : ℕ := (b2TW.getD k []).getD (2 * c + c') 0

/-- Digit `i` of a 12-bit word. -/
def wbit (w : ℕ) (i : Fin 12) : ZMod 2 := ((w / 2 ^ (11 - (i : ℕ)) % 2 : ℕ) : ZMod 2)

/-- The table is the law: for `1 ≤ l ≤ 63`, `D_i(l) = ` tuple `b2Idx[l − 1]`. -/
theorem b2_table : ∀ l : Fin 63, b2Idx.getD l 0 < 35 ∧ ∀ i : Fin 12, ∀ c c' : Fin 2,
    b2lawC i (l + 1) c c' = wbit (b2w (b2Idx.getD l 0) c c') i := by
  decide +kernel

/-- `σ_c` of `lem:cert` for the step pattern `(f_0, f_1) ∈ {0,1}²` and the tuples `k_0` (carry of
coordinate `0`), `k_1` (carry of coordinate `1`): `σ_{c,i} = f_0 D_i(l_0)[c][0] + f_1 D_i(l_1)[c][1]`. -/
def b2sig (k0 k1 f0 f1 : ℕ) (c : Fin 2) : Fin 12 → ZMod 2 :=
  fun i => (f0 : ZMod 2) * wbit (b2w k0 c 0) i + (f1 : ZMod 2) * wbit (b2w k1 c 1) i

/-- **The certificate minimum** (`thm:B2`, `j = 12`): over all pairs of the 35 tuples and all step
patterns, `∑_c (2^12 f_12(e_c, σ_c))² ≥ 2269618` (lower bounds `gapLB`). -/
theorem b2_check : ∀ k0 k1 : Fin 35, ∀ f0 f1 : Fin 2, (f0 ≠ 0 ∨ f1 ≠ 0) →
    2269618 ≤ gapLB f0 (b2sig k0 k1 f0 f1 0) ^ 2 + gapLB f1 (b2sig k0 k1 f0 f1 1) ^ 2 := by
  decide +kernel

/-- Distinctness of the 35 tuples (as digit vectors). -/
theorem b2_distinct : ∀ k k' : Fin 35, k ≠ k' →
    ∃ i : Fin 12, ∃ c c' : Fin 2, wbit (b2w k c c') i ≠ wbit (b2w k' c c') i := by
  decide +kernel

/-- Every one of the 35 tuples occurs for some `1 ≤ l ≤ 63`. -/
theorem b2_onto : ∀ k : Fin 35, ∃ l : Fin 63, b2Idx.getD l 0 = k := by
  decide +kernel

/-! ## The certificate in terms of `gapNum` and the law -/

lemma intCast_zmod2 (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) : ((e : ℤ) : ZMod 2) = ((e.natAbs : ℕ) : ZMod 2) := by
  rcases (show e = -1 ∨ e = 0 ∨ e = 1 by omega) with rfl | rfl | rfl <;> decide

/-- The responses for `1 ≤ l ≤ 63` from the table. -/
lemma lawD_tab (i : Fin 12) (l : ℕ) (hl1 : 1 ≤ l) (hl2 : l ≤ 63) (c c' : Fin 2) :
    lawD B2g B2z B2G i l c c' = wbit (b2w (b2Idx.getD (l - 1) 0) c c') i := by
  have h := (b2_table ⟨l - 1, by omega⟩).2 i c c'
  simp only [show l - 1 + 1 = l by omega] at h
  rw [lawD_B2 i l hl1, h]

lemma idx_lt (l : ℕ) (hl1 : 1 ≤ l) (hl2 : l ≤ 63) : b2Idx.getD (l - 1) 0 < 35 :=
  (b2_table ⟨l - 1, by omega⟩).1

/-- `σ_c` of `lem:cert` for carry lengths in `[1, 63]`. -/
lemma sig_tab (e : Fin 2 → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (l : Fin 2 → ℕ)
    (hl1 : ∀ c, 1 ≤ l c) (hl2 : ∀ c, l c ≤ 63) (c : Fin 2) :
    certSigmaP (lawD B2g B2z B2G) 12 e l c =
      b2sig (b2Idx.getD (l 0 - 1) 0) (b2Idx.getD (l 1 - 1) 0) (e 0).natAbs (e 1).natAbs c := by
  funext i
  simp only [certSigmaP, b2sig, Fin.sum_univ_two]
  rw [lawD_tab i (l 0) (hl1 0) (hl2 0), lawD_tab i (l 1) (hl1 1) (hl2 1),
    intCast_zmod2 (e 0) (he 0), intCast_zmod2 (e 1) (he 1)]

set_option maxRecDepth 100000 in
/-- The binding case, own coordinate: the witness `R = σ_0` gives `|2^12 + enc(0) − enc(σ_0)| − 1 = 103`. -/
lemma b2_v0 : ((1 : ℤ) * ((2 : ℕ) : ℤ) ^ 12 +
    (encVec (zcode 2) (b2sig 0 0 1 0 0 + b2sig 0 0 1 0 0) : ℤ) -
      (encVec (zcode 2) (b2sig 0 0 1 0 0) : ℤ)).natAbs - 1 = 103 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The binding case, cross coordinate: the witness `R = 001000100000` gives `1504 − 1 = 1503`. -/
lemma b2_v1 : ((0 : ℤ) * ((2 : ℕ) : ℤ) ^ 12 +
    (encVec (zcode 2) ((fun i => wbit 544 i) + b2sig 0 0 1 0 1) : ℤ) -
      (encVec (zcode 2) (fun i => wbit 544 i) : ℤ)).natAbs - 1 = 1503 := by decide +kernel

/-- The lower bound half of `B2_cert_min`. -/
lemma B2_cert_lb (e : Fin 2 → ℤ) (l : Fin 2 → ℕ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    2269618 ≤ ∑ c, gapNum (zcode 2) 12 (e c) (certSigmaP (lawD B2g B2z B2G) 12 e l c) ^ 2 := by
  obtain ⟨l0, h01, h02, hq0⟩ := B2_octave (l 0) (hl 0)
  obtain ⟨l1, h11, h12, hq1⟩ := B2_octave (l 1) (hl 1)
  have hsig : ∀ c, certSigmaP (lawD B2g B2z B2G) 12 e l c =
      b2sig (b2Idx.getD (l0 - 1) 0) (b2Idx.getD (l1 - 1) 0) (e 0).natAbs (e 1).natAbs c := by
    intro c
    have hs := sig_tab e he ![l0, l1] (fun c => by fin_cases c <;> simp [h01, h11])
      (fun c => by fin_cases c <;> simp [h02, h12]) c
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    rewrite [← hs]
    funext i
    simp only [certSigmaP, Fin.sum_univ_two]
    rw [hq0 i i.isLt c 0, hq1 i i.isLt c 1]
    rfl
  rewrite [Fin.sum_univ_two, hsig 0, hsig 1]
  have hk0 := idx_lt l0 h01 h02
  have hk1 := idx_lt l1 h11 h12
  have he0 : (e 0).natAbs < 2 := by have := he 0; omega
  have he1 : (e 1).natAbs < 2 := by have := he 1; omega
  have hne' : (⟨(e 0).natAbs, he0⟩ : Fin 2) ≠ 0 ∨ (⟨(e 1).natAbs, he1⟩ : Fin 2) ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    fin_cases c
    · left; intro h; apply hc; simpa [Fin.ext_iff] using h
    · right; intro h; apply hc; simpa [Fin.ext_iff] using h
  have hc := b2_check ⟨_, hk0⟩ ⟨_, hk1⟩ ⟨_, he0⟩ ⟨_, he1⟩ hne'
  exact hc.trans (Nat.add_le_add (Nat.pow_le_pow_left (gapLB_le _ (he 0) _) 2)
    (Nat.pow_le_pow_left (gapLB_le _ (he 1) _) 2))

lemma sum_two_sq_le (F : Fin 2 → ℕ) (h0 : F 0 ≤ 103) (h1 : F 1 ≤ 1503) :
    ∑ c, F c ^ 2 ≤ 2269618 := by
  rw [Fin.sum_univ_two]
  have a := Nat.pow_le_pow_left h0 2
  have b := Nat.pow_le_pow_left h1 2
  norm_num at a b ⊢
  omega

/-- **`thm:B2`, the certificate minimum** (`lem:cert`, `q = 2`, `j = 12`; computer-assisted in the
paper): for every step `e ∈ {-1,0,1}² ∖ {0}` and all carry lengths `l_c ≥ 1`,
`∑_c (2^12 f_12(e_c, σ_c))² ≥ 2269618`, and the value `2269618 = 103² + 1503²` is attained at the
horizontal step `e = (1, 0)` with carry length `1`. -/
theorem B2_cert_min :
    (∀ (e : Fin 2 → ℤ) (l : Fin 2 → ℕ), (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
      (∀ c, 1 ≤ l c) →
        2269618 ≤ ∑ c, gapNum (zcode 2) 12 (e c) (certSigmaP (lawD B2g B2z B2G) 12 e l c) ^ 2) ∧
    ∑ c, gapNum (zcode 2) 12 (![1, 0] c) (certSigmaP (lawD B2g B2z B2G) 12 ![1, 0] ![1, 1] c) ^ 2 =
      2269618 := by
  refine ⟨B2_cert_lb, le_antisymm ?_ (B2_cert_lb _ _ (fun c => by fin_cases c <;> simp)
    ⟨0, by simp⟩ (fun c => by fin_cases c <;> simp))⟩
  have h1 := sig_tab ![1, 0] (fun c => by fin_cases c <;> simp) ![1, 1]
    (fun c => by fin_cases c <;> simp) (fun c => by fin_cases c <;> simp)
  have hi : b2Idx.getD ((![1, 1] : Fin 2 → ℕ) 0 - 1) 0 = 0 := by decide
  have hi' : b2Idx.getD ((![1, 1] : Fin 2 → ℕ) 1 - 1) 0 = 0 := by decide
  have hF0 := (gapNum_le (zcode 2) 12 _ (certSigmaP (lawD B2g B2z B2G) 12 ![1, 0] ![1, 1] 0)
    (b2sig 0 0 1 0 0)).trans (le_of_eq (by
      rewrite [h1 0, hi, hi']
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.natAbs_one, Int.natAbs_zero]
      exact b2_v0))
  have hF1 := (gapNum_le (zcode 2) 12 _ (certSigmaP (lawD B2g B2z B2G) 12 ![1, 0] ![1, 1] 1)
    (fun i => wbit 544 i)).trans (le_of_eq (by
      rewrite [h1 1, hi, hi']
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.natAbs_one, Int.natAbs_zero]
      exact b2_v1))
  exact sum_two_sq_le _ hF0 hF1

/-- **`lem:octave`, the count**: for `j = 12` the tuples `(D_i(l))_{i<12}`, `1 ≤ l ≤ 63` (hence, by
`B2_octave`, all `l ≥ 1`), take exactly `35` distinct values. -/
theorem B2_octave_count :
    ((Finset.Icc 1 63).image fun l => fun (i : Fin 12) (c c' : Fin 2) => lawD B2g B2z B2G i l c c').card
      = 35 := by
  let T : Fin 35 → (Fin 12 → Fin 2 → Fin 2 → ZMod 2) := fun k i c c' => wbit (b2w k c c') i
  have himg : ((Finset.Icc 1 63).image fun l => fun (i : Fin 12) (c c' : Fin 2) =>
      lawD B2g B2z B2G i l c c') = Finset.univ.image T := by
    ext t
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, ⟨hl1, hl2⟩, rfl⟩
      refine ⟨⟨_, idx_lt l hl1 hl2⟩, ?_⟩
      funext i c c'
      exact (lawD_tab i l hl1 hl2 c c').symm
    · rintro ⟨k, rfl⟩
      obtain ⟨l, hl⟩ := b2_onto k
      refine ⟨(l : ℕ) + 1, ⟨by omega, by omega⟩, ?_⟩
      funext i c c'
      rw [lawD_tab i _ (by omega) (by omega), show (l : ℕ) + 1 - 1 = l by omega, hl]
  rw [himg, Finset.card_image_of_injective _ (fun k k' hkk' => ?_), Finset.card_univ,
    Fintype.card_fin]
  by_contra hne
  obtain ⟨i, c, c', h⟩ := b2_distinct k k' hne
  exact h (congrFun (congrFun (congrFun hkk' i) c) c')

/-! ## The level `K = 1` (`q^K < 4`): a direct check of the four points of `P_2` -/

/-- The first eight digits of the points `y(v)`, `v < 4`, as an integer (computable entries of
`B2gen` from the truncated series of `GeoSeq/Fidelity.lean`). -/
def b2cell8 (v : ℕ) (c : Fin 2) : ℕ :=
  ∑ n : Fin 8, (∑ k ∈ range (v + 1),
    cget (tcols 8 4 (![b2g0L 8, b2g1L 8] c) (![uL 8, b2z1L 8] c)) k n *
      idxDigit (zcode 2) v k).val * 2 ^ (8 - 1 - (n : ℕ))

lemma cell8 (v : ℕ) (hv : v < 4) (c : Fin 2) : cellIdx (zcode 2) B2gen v c 8 = b2cell8 v c := by
  unfold cellIdx b2cell8
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [z2enc]
  congr 2
  unfold seqDigit
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 4 := by have := Finset.mem_range.mp hk; omega
  rw [show B2gen c n k = _ from ssGen_entry B2g B2z c (b2g_rep 8 c) (b2z_rep 8 c) n k n.isLt hk']

/-- Every two of the four points of `P_2` are at least `80` eight-digit cells apart in one coordinate
(on the circle of `256` cells). -/
theorem b2_cell8_far : ∀ v w : Fin 4, v ≠ w → ∃ c : Fin 2,
    80 ≤ ((b2cell8 v c : ℤ) - b2cell8 w c).natAbs ∧
      ((b2cell8 v c : ℤ) - b2cell8 w c).natAbs + 80 ≤ 256 := by
  decide +kernel

/-- Cells at circular distance at least `M` give a toroidal coordinate gap of at least `(M-1)/Q`. -/
lemma tor_cells {Q a b A B M : ℝ} (hQ : 0 < Q) (ha1 : A ≤ Q * a) (ha2 : Q * a ≤ A + 1)
    (hb1 : B ≤ Q * b) (hb2 : Q * b ≤ B + 1) (h1 : M ≤ |A - B|) (h2 : |A - B| + M ≤ Q) :
    (M - 1) / Q ≤ Z3NetDGS.torCoord a b := by
  have hx : |Q * a - Q * b - (A - B)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hlo := abs_sub_abs_le_abs_sub (Q * a - Q * b) (A - B)
  have hhi := abs_sub_abs_le_abs_sub (A - B) (Q * a - Q * b)
  rw [abs_sub_comm (A - B)] at hhi
  have hm : |Q * a - Q * b| = Q * |a - b| := by
    rw [← mul_sub, abs_mul, abs_of_pos hQ]
  rw [hm] at hlo hhi
  unfold Z3NetDGS.torCoord
  apply le_min
  · rw [div_le_iff₀ hQ]; nlinarith
  · rw [div_le_iff₀ hQ]; nlinarith

/-- **`thm:B2`, level `K = 1`**: the four points of `P_2` have `c(P_2) ≥ √2269618/4096` (in fact every
pair has a coordinate with toroidal gap `≥ 79/256`, so `c(P_2) ≥ 158/256`). -/
theorem B2_sep_one : SepAtLevel 2 2 1 (seqPoint (zcode 2) B2gen) (Real.sqrt 2269618 / 4096) := by
  intro v w hv hw hvw
  have hv4 : v < 4 := by simpa using hv
  have hw4 : w < 4 := by simpa using hw
  obtain ⟨c, hc1, hc2⟩ := b2_cell8_far ⟨v, hv4⟩ ⟨w, hw4⟩ (fun h => hvw (congrArg Fin.val h))
  have cv := coord_cell (le_refl 2) (zcode 2) B2gen v c 8
  have cw := coord_cell (le_refl 2) (zcode 2) B2gen w c 8
  rw [cell8 v hv4] at cv
  rw [cell8 w hw4] at cw
  simp only [Fin.val_mk] at hc1 hc2
  zify at hc1 hc2
  have hd1 : (80 : ℝ) ≤ |(b2cell8 v c : ℝ) - b2cell8 w c| := by exact_mod_cast hc1
  have hd2 : |(b2cell8 v c : ℝ) - b2cell8 w c| + 80 ≤ (2 : ℝ) ^ 8 := by
    norm_num; exact_mod_cast hc2
  have ht := tor_cells (Q := (2 : ℝ) ^ 8) (by positivity) (by exact_mod_cast cv.1) (by exact_mod_cast cv.2)
    (by exact_mod_cast cw.1) (by exact_mod_cast cw.2) hd1 hd2
  -- the toroidal distance is at least one coordinate gap
  have hT : Z3NetDGS.torCoord (seqPoint (zcode 2) B2gen v c) (seqPoint (zcode 2) B2gen w c) ≤
      Z3NetDGS.torDist2 (seqPoint (zcode 2) B2gen v) (seqPoint (zcode 2) B2gen w) := by
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => Z3NetDGS.torCoord (seqPoint (zcode 2) B2gen v j)
      (seqPoint (zcode 2) B2gen w j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ c)
  have hs : Real.sqrt 2269618 ≤ 2528 := by
    rw [show (2528 : ℝ) = Real.sqrt (2528 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  push_cast
  norm_num at ht
  nlinarith

/-! ## `thm:B2` -/

lemma B2_LB_le_one : Real.sqrt 2269618 / 4096 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  rw [show (4096 : ℝ) = Real.sqrt (4096 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma B2_LB_pos : 0 < Real.sqrt 2269618 / 4096 := by positivity

/-- **`thm:B2`** (separation): `c(P_{2K}) ≥ √2269618/4096 = 0.36780…` for every `K ≥ 1`. -/
theorem B2_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 2 2 K (seqPoint (zcode 2) B2gen) (Real.sqrt 2269618 / 4096) := by
  rcases Nat.lt_or_ge K 2 with h | h
  · obtain rfl : K = 1 := by omega
    exact B2_sep_one
  have hK4 : 4 ≤ 2 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
  have hc := cert_prime B2gen K 12 hK4 (B2_net (2 * K) 0) (lawD B2g B2z B2G)
    (fun i _ l h1 h2 c c' => B2_law K i l h1 h2 c c') (Real.sqrt 2269618 / 4096) ?_
  · rwa [min_eq_right B2_LB_le_one] at hc
  rintro e l ⟨he, hne, hl⟩
  have hb := B2_cert_lb e l he hne (fun c => (hl c).1)
  rewrite [Fin.sum_univ_two] at hb
  unfold certTerm
  rewrite [Fin.sum_univ_two]
  generalize gapNum (zcode 2) 12 (e 0) (certSigmaP (lawD B2g B2z B2G) 12 e l 0) = A at hb ⊢
  generalize gapNum (zcode 2) 12 (e 1) (certSigmaP (lawD B2g B2z B2G) 12 e l 1) = B at hb ⊢
  apply Real.le_sqrt_of_sq_le
  have hb' : (2269618 : ℝ) ≤ (A : ℝ) ^ 2 + (B : ℝ) ^ 2 := by exact_mod_cast hb
  rw [div_pow, Real.sq_sqrt (by norm_num), div_pow, div_pow, ← add_div]
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

lemma sepAllN_mono {s : ℕ} (pt : ℕ → Fin s → ℝ) {b b' : ℝ} (hb : b' ≤ b) (h : SepAllN s pt b) :
    SepAllN s pt b' := by
  intro N hN v w hv hw hvw
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / (s : ℝ))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact (mul_le_mul_of_nonneg_right hb hN0).trans (h N hN v w hv hw hvw)

/-- **`thm:B2`** (all `N`): `δ(P_{[N]}) ≥ 0.1839 · N^{-1/2}` for every `N ≥ 2`. -/
theorem B2_allN : SepAllN 2 (seqPoint (zcode 2) B2gen) (1839 / 10000) := by
  have h := prefix_sep 2 2 (le_refl 2) (by norm_num) (seqPoint (zcode 2) B2gen) _ B2_LB_pos.le
    (fun K hK => B2_sep K hK)
  refine sepAllN_mono _ ?_ h
  have hs : (15065088 / 10000 : ℝ) ≤ Real.sqrt 2269618 := Real.le_sqrt_of_sq_le (by norm_num)
  push_cast
  rw [div_div, le_div_iff₀ (by norm_num)]
  nlinarith

/-- **`thm:B2`** (mesh ratio): `h(P_{[N]}) ≤ 7.7 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal; `15.4` in the convention `h/(δ/2)` of [DGS2]). -/
theorem B2_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 2) B2gen)) ≤
      (77 / 10) * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 2) B2gen))) := by
  have h := prefix_mesh (zcode 2) B2gen (le_refl 2) (by norm_num) B2_net _ B2_LB_pos
    (fun K hK => B2_sep K hK) N hN
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h2 : Real.sqrt 2 ≤ 141422 / 100000 := by
      rw [show (141422 / 100000 : ℝ) = Real.sqrt ((141422 / 100000) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs : (15065 / 10 : ℝ) ≤ Real.sqrt 2269618 := Real.le_sqrt_of_sq_le (by norm_num)
    push_cast
    rw [div_le_iff₀ B2_LB_pos]
    nlinarith
  · have : 0 ≤ Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 2) B2gen)) :=
      Real.iInf_nonneg fun _ => div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    linarith

end GeoSeq
