/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B3Law
public import GeoSeq.B3Data
public import GeoSeq.B2Cert
public import GeoSeq.WFLaw

@[expose] public section

/-!
# GeoSeq stage S6: the exact response sets and the certificate of `thm:B3`

* The automaton certificate (`prop:automaton` for `thm:B3`, per source coordinate `c'` of the carry):
  the initial vector, closure of the state lists under the three Cartier steps, readouts, witnesses
  (kernel `decide`).
* `B3_resp`: for every carry length `l ≥ 1` the column `(D_i(l)[c][c'])_{i<6, c<2}` is one of the
  listed tuples (`24` for `c' = 0`, `36` for `c' = 1`); `B3_resp_card`: exactly these occur.
* Base-3 closed forms for `f_j` (lower bounds) and the certificate minimum
  `37865 = 91² + 172² = min ∑_c (3^6 f_6(e_c, σ_c))²` (`B3_cert_min`, attained at the antidiagonal
  step `e = (-1, 1)`), `B3_sep_one` (`K = 1`, direct check of the nine points of `P_2`), and
  `thm:B3`: `B3_sep`, `B3_allN`, `B3_mesh`; `cor:allprimes`.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## The automaton certificate, column `c' = 0` -/

set_option maxRecDepth 100000 in
theorem b3_init0 : B3B0.getD 0 [] = initV 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_closeA0 : ∀ s : Fin 34, ∀ r : Fin 3, (B3tA0.getD s []).getD r 0 < 34 ∧
    stepV r (B3A0.getD s []) = B3A0.getD ((B3tA0.getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_closeB0 : ∀ s : Fin 3, ((B3tB0.getD s []).getD 0 0 < 3 ∧
    stepV 0 (B3B0.getD s []) = B3B0.getD ((B3tB0.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 3, r ≠ 0 → (B3tB0.getD s []).getD r 0 < 34 ∧
      stepV r (B3B0.getD s []) = B3A0.getD ((B3tB0.getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_read0 : ∀ s : Fin 34, B3out0.getD s 0 < 24 ∧
    (B3A0.getD s []).map acoef = B3tup0.getD (B3out0.getD s 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_wit0 : ∀ t : Fin 24, (∀ d ∈ B3wit0.getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 (B3wit0.getD t []) ∧
    (readV (B3wit0.getD t []) (initV 0)).map acoef = B3tup0.getD t [] := by decide +kernel

/-! ## The automaton certificate, column `c' = 1` -/

set_option maxRecDepth 100000 in
theorem b3_init1 : B3B1.getD 0 [] = initV 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_closeA1 : ∀ s : Fin 87, ∀ r : Fin 3, (B3tA1.getD s []).getD r 0 < 87 ∧
    stepV r (B3A1.getD s []) = B3A1.getD ((B3tA1.getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_closeB1 : ∀ s : Fin 4, ((B3tB1.getD s []).getD 0 0 < 4 ∧
    stepV 0 (B3B1.getD s []) = B3B1.getD ((B3tB1.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 3, r ≠ 0 → (B3tB1.getD s []).getD r 0 < 87 ∧
      stepV r (B3B1.getD s []) = B3A1.getD ((B3tB1.getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_read1 : ∀ s : Fin 87, B3out1.getD s 0 < 36 ∧
    (B3A1.getD s []).map acoef = B3tup1.getD (B3out1.getD s 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_wit1 : ∀ t : Fin 36, (∀ d ∈ B3wit1.getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 (B3wit1.getD t []) ∧
    (readV (B3wit1.getD t []) (initV 1)).map acoef = B3tup1.getD t [] := by decide +kernel

/-! ## The response sets (`prop:automaton` for `thm:B3`) -/

lemma vals_initV (c' : Fin 2) (l i : ℕ) (hi : i < 6) (c : Fin 2) :
    (vals (initV c') l).getD (2 * i + c) 0 = lawD B3g B3z B3G i l c c' := by
  have hk : 2 * i + (c : ℕ) < 12 := by omega
  unfold vals initV
  rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some, Function.comp_apply]
  have h1 : (2 * i + (c : ℕ)) / 2 = i := by omega
  have h2 : (if (2 * i + (c : ℕ)) % 2 = 0 then (0 : Fin 2) else 1) = c := by
    fin_cases c
    · simp
    · simp only [Fin.mk_one, Fin.isValue, Fin.val_one]
      rw [if_neg (by omega)]
  rw [h1, h2]
  exact B3_init i hi c c' l

/-- From an automaton certificate to the response set of a column. -/
theorem resp_of_cert (c' : Fin 2) (A B : List (List St3)) (tA tB : List (List ℕ)) (out : List ℕ)
    (tup : List (List (ZMod 3))) (N M T : ℕ) (hN : A.length = N) (hM : B.length = M) (hM0 : 0 < M)
    (hinit : B.getD 0 [] = initV c')
    (hA : ∀ s : Fin N, ∀ r : Fin 3, (tA.getD s []).getD r 0 < N ∧
      stepV r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepV 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepV r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) [])
    (hread : ∀ s : Fin N, out.getD s 0 < T ∧ (A.getD s []).map acoef = tup.getD (out.getD s 0) [])
    (l : ℕ) (hl : 1 ≤ l) : ∃ t < T, vals (initV c') l = tup.getD t [] := by
  obtain ⟨s', hs', h⟩ := reach_B A B tA tB N M hN hM hA hB l 0 hl hM0
  rw [hinit] at h
  obtain ⟨h1, h2⟩ := hread ⟨s', hs'⟩
  exact ⟨_, h1, by rw [h, vals_zero]; exact h2⟩

/-- **`prop:automaton` for `thm:B3`** (`j = 6`): for every carry length `l ≥ 1` and source coordinate
`c'`, the column of responses `(D_i(l)[c][c'])_{i<6, c<2}` is one of the `B3ntup c'` listed tuples. -/
theorem B3_resp (c' : Fin 2) (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < B3ntup c', ∀ i < 6, ∀ c : Fin 2, lawD B3g B3z B3G i l c c' = B3tupv c' t i c := by
  have key : ∃ t < B3ntup c', vals (initV c') l = (![B3tup0, B3tup1] c').getD t [] := by
    fin_cases c'
    · exact resp_of_cert 0 B3A0 B3B0 B3tA0 B3tB0 B3out0 B3tup0 34 3 24 (by decide +kernel)
        (by decide +kernel) (by norm_num) b3_init0 b3_closeA0 b3_closeB0 b3_read0 l hl
    · exact resp_of_cert 1 B3A1 B3B1 B3tA1 B3tB1 B3out1 B3tup1 87 4 36 (by decide +kernel)
        (by decide +kernel) (by norm_num) b3_init1 b3_closeA1 b3_closeB1 b3_read1 l hl
  obtain ⟨t, ht, h⟩ := key
  refine ⟨t, ht, fun i hi c => ?_⟩
  rw [← vals_initV c' l i hi c, h]; rfl

/-- **`prop:automaton` for `thm:B3`, exactness**: every listed tuple occurs for some `l ≥ 1`. -/
theorem B3_resp_occurs (c' : Fin 2) (t : ℕ) (ht : t < B3ntup c') :
    ∃ l, 1 ≤ l ∧ ∀ i < 6, ∀ c : Fin 2, lawD B3g B3z B3G i l c c' = B3tupv c' t i c := by
  have key : ∃ ds : List ℕ, (∀ d ∈ ds, d < 3) ∧ 1 ≤ Nat.ofDigits 3 ds ∧
      (readV ds (initV c')).map acoef = (![B3tup0, B3tup1] c').getD t [] := by
    fin_cases c'
    · exact ⟨_, b3_wit0 ⟨t, ht⟩⟩
    · exact ⟨_, b3_wit1 ⟨t, ht⟩⟩
  obtain ⟨ds, hds, h1, h2⟩ := key
  refine ⟨Nat.ofDigits 3 ds, h1, fun i hi c => ?_⟩
  rw [← vals_initV c' _ i hi c, vals_read ds hds, vals_zero, h2]; rfl

set_option maxRecDepth 100000 in
theorem b3_distinct0 : ∀ t t' : Fin 24, t ≠ t' →
    ∃ i : Fin 6, ∃ c : Fin 2, B3tupv 0 t i c ≠ B3tupv 0 t' i c := by decide +kernel

set_option maxRecDepth 100000 in
theorem b3_distinct1 : ∀ t t' : Fin 36, t ≠ t' →
    ∃ i : Fin 6, ∃ c : Fin 2, B3tupv 1 t i c ≠ B3tupv 1 t' i c := by decide +kernel

/-- **`prop:automaton` for `thm:B3`, the count** (`j = 6`): the columns of responses over all carry
lengths `l ≥ 1` form a set of exactly `24` (`c' = 0`) resp. `36` (`c' = 1`) elements. -/
theorem B3_resp_card (c' : Fin 2) :
    Set.ncard {D : Fin 6 → Fin 2 → ZMod 3 |
      ∃ l, 1 ≤ l ∧ ∀ i : Fin 6, ∀ c : Fin 2, D i c = lawD B3g B3z B3G i l c c'} = B3ntup c' := by
  let f : Fin (B3ntup c') → (Fin 6 → Fin 2 → ZMod 3) := fun t i c => B3tupv c' t i c
  have hset : {D : Fin 6 → Fin 2 → ZMod 3 |
      ∃ l, 1 ≤ l ∧ ∀ i : Fin 6, ∀ c : Fin 2, D i c = lawD B3g B3z B3G i l c c'} = Set.range f := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨l, hl, hD⟩
      obtain ⟨t, ht, h⟩ := B3_resp c' l hl
      exact ⟨⟨t, ht⟩, funext fun i => funext fun c => by rw [hD, h i i.isLt c]⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨l, hl, h⟩ := B3_resp_occurs c' t ht
      exact ⟨l, hl, fun i c => (h i i.isLt c).symm⟩
  have hinj : Function.Injective f := by
    intro t t' htt
    by_contra hne
    have hd : ∃ i : Fin 6, ∃ c : Fin 2, B3tupv c' t i c ≠ B3tupv c' t' i c := by
      fin_cases c'
      · exact b3_distinct0 t t' hne
      · exact b3_distinct1 t t' hne
    obtain ⟨i, c, h⟩ := hd
    exact h (congrFun (congrFun htt i) c)
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## `f_j` in base three: lower bounds by the digits of `σ` -/

lemma z3enc (x : ZMod 3) : ((zcode 3).enc x : ℕ) = x.val := rfl

lemma z3_digit (a b : ZMod 3) :
    ((a + b).val : ℤ) - a.val ≤ b.val ∧ -((2 * b).val : ℤ) ≤ (a + b).val - a.val := by
  revert a b; decide

/-- `-enc(-σ) ≤ enc(R ⊕ σ) - enc(R) ≤ enc(σ)` in base three (`-σ = 2σ`). -/
lemma enc_diff3 {j : ℕ} (r σ : Fin j → ZMod 3) :
    (encVec (zcode 3) (r + σ) : ℤ) - encVec (zcode 3) r ≤ encVec (zcode 3) σ ∧
    -(encVec (zcode 3) (fun i => 2 * σ i) : ℤ) ≤ (encVec (zcode 3) (r + σ) : ℤ) - encVec (zcode 3) r := by
  induction j with
  | zero => simp [encVec_zero]
  | succ j ih =>
    rw [encVec_succ, encVec_succ, encVec_succ (zcode 3) σ, encVec_succ (zcode 3) (fun i => 2 * σ i)]
    have ht : Fin.tail (r + σ) = Fin.tail r + Fin.tail σ := rfl
    have ht2 : Fin.tail (fun i => 2 * σ i) = fun i => 2 * Fin.tail σ i := rfl
    rw [ht, ht2]
    obtain ⟨d1, d2⟩ := z3_digit (r 0) (σ 0)
    obtain ⟨i1, i2⟩ := ih (Fin.tail r) (Fin.tail σ)
    simp only [z3enc, Pi.add_apply] at d1 d2 i1 i2 ⊢
    push_cast
    have hp : (0 : ℤ) ≤ 3 ^ j := by positivity
    have m1 := mul_le_mul_of_nonneg_right d1 hp
    have m2 := mul_le_mul_of_nonneg_right d2 hp
    constructor <;> nlinarith

lemma gapNum3_pos (j : ℕ) (σ : Fin j → ZMod 3) :
    3 ^ j - encVec (zcode 3) (fun i => 2 * σ i) - 1 ≤ gapNum (zcode 3) j 1 σ := by
  apply gapNum_ge
  intro r
  obtain ⟨_, h2⟩ := enc_diff3 r σ
  have hlt := encVec_lt (zcode 3) (fun i => 2 * σ i)
  zify [hlt.le]
  rw [le_abs]; left; push_cast; linarith

lemma gapNum3_neg (j : ℕ) (σ : Fin j → ZMod 3) :
    3 ^ j - encVec (zcode 3) σ - 1 ≤ gapNum (zcode 3) j (-1) σ := by
  apply gapNum_ge
  intro r
  obtain ⟨h1, _⟩ := enc_diff3 r σ
  have hlt := encVec_lt (zcode 3) σ
  zify [hlt.le]
  rw [le_abs]; right; push_cast; linarith

/-- The bound for `e = 0`: with `σ_t` the leading nonzero digit and `ρ` the digits after it,
`3^k - enc(-ρ)` if `σ_t = 1` and `3^k - enc(ρ)` if `σ_t = 2` (`k` = number of digits after `t`). -/
def top3 : (j : ℕ) → (Fin j → ZMod 3) → ℕ
  | 0, _ => 0
  | j + 1, σ => if σ 0 = 0 then top3 j (Fin.tail σ)
      else if σ 0 = 1 then 3 ^ j - encVec (zcode 3) (fun i => 2 * Fin.tail σ i)
      else 3 ^ j - encVec (zcode 3) (Fin.tail σ)

lemma z3_d0 (a : ZMod 3) : ((a + 0).val : ℤ) - a.val = 0 := by revert a; decide
lemma z3_d1 (a : ZMod 3) : ((a + 1).val : ℤ) - a.val = 1 ∨ ((a + 1).val : ℤ) - a.val = -2 := by
  revert a; decide
lemma z3_d2 (a : ZMod 3) : ((a + 2).val : ℤ) - a.val = 2 ∨ ((a + 2).val : ℤ) - a.val = -1 := by
  revert a; decide
lemma z3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by revert x; decide

lemma top3_le {j : ℕ} (r σ : Fin j → ZMod 3) :
    (top3 j σ : ℤ) ≤ |(encVec (zcode 3) (r + σ) : ℤ) - encVec (zcode 3) r| := by
  induction j with
  | zero => simp [top3]
  | succ j ih =>
    rw [encVec_succ, encVec_succ]
    have ht : Fin.tail (r + σ) = Fin.tail r + Fin.tail σ := rfl
    rw [ht]
    obtain ⟨b1, b2⟩ := enc_diff3 (Fin.tail r) (Fin.tail σ)
    have l1 := encVec_lt (zcode 3) (Fin.tail σ)
    have l2 := encVec_lt (zcode 3) (fun i => 2 * Fin.tail σ i)
    simp only [z3enc, Pi.add_apply] at b1 b2 ⊢
    push_cast
    set B := (encVec (zcode 3) (Fin.tail r + Fin.tail σ) : ℤ) - encVec (zcode 3) (Fin.tail r)
    have e : ((r 0 + σ 0).val : ℤ) * 3 ^ j + encVec (zcode 3) (Fin.tail r + Fin.tail σ) -
        ((r 0).val * 3 ^ j + encVec (zcode 3) (Fin.tail r)) =
        (((r 0 + σ 0).val : ℤ) - (r 0).val) * 3 ^ j + B := by simp only [B]; ring
    rw [e]
    have hP : (0 : ℤ) < 3 ^ j := by positivity
    have l1' : (encVec (zcode 3) (Fin.tail σ) : ℤ) < 3 ^ j := by exact_mod_cast l1
    have l2' : (encVec (zcode 3) (fun i => 2 * Fin.tail σ i) : ℤ) < 3 ^ j := by exact_mod_cast l2
    have n1 : (0 : ℤ) ≤ encVec (zcode 3) (Fin.tail σ) := by positivity
    have n2 : (0 : ℤ) ≤ encVec (zcode 3) (fun i => 2 * Fin.tail σ i) := by positivity
    rcases z3_cases (σ 0) with h | h | h
    · simp only [top3, h, ite_true]
      rw [z3_d0, zero_mul, zero_add]
      exact ih (Fin.tail r) (Fin.tail σ)
    · simp only [top3, h, ite_true, show (1 : ZMod 3) ≠ 0 by decide, ite_false]
      rw [Nat.cast_sub l2.le]; push_cast
      rcases z3_d1 (r 0) with hd | hd <;> rw [hd]
      · rw [le_abs]; left; linarith
      · rw [le_abs]; right; linarith
    · simp only [top3, h, show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide,
        ite_false]
      rw [Nat.cast_sub l1.le]; push_cast
      rcases z3_d2 (r 0) with hd | hd <;> rw [hd]
      · rw [le_abs]; left; linarith
      · rw [le_abs]; right; linarith

lemma gapNum3_zero (j : ℕ) (σ : Fin j → ZMod 3) : top3 j σ - 1 ≤ gapNum (zcode 3) j 0 σ := by
  apply gapNum_ge
  intro r
  have h := top3_le r σ
  zify
  simpa using h

/-! ## The certificate minimum -/

/-- The certificate lower bound for one coordinate by the code `f` of `e` (`0 ↦ 0`, `1 ↦ 1`,
`2 ↦ -1`). -/
def gapLB3 (f : ℕ) (σ : Fin 6 → ZMod 3) : ℕ :=
  (if f = 0 then top3 6 σ else if f = 1 then 3 ^ 6 - encVec (zcode 3) (fun i => 2 * σ i)
    else 3 ^ 6 - encVec (zcode 3) σ) - 1

/-- The code of a step entry `e ∈ {-1, 0, 1}`. -/
def fcode (e : ℤ) : ℕ := if e = 0 then 0 else if e = 1 then 1 else 2

/-- The value in `𝔽_3` of the code. -/
def emod3 (f : ℕ) : ZMod 3 := if f = 0 then 0 else if f = 1 then 1 else 2

lemma gapLB3_le (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (σ : Fin 6 → ZMod 3) :
    gapLB3 (fcode e) σ ≤ gapNum (zcode 3) 6 e σ := by
  unfold gapLB3 fcode
  rcases (show e = -1 ∨ e = 0 ∨ e = 1 by omega) with rfl | rfl | rfl
  · simpa using gapNum3_neg 6 σ
  · simpa using gapNum3_zero 6 σ
  · simpa using gapNum3_pos 6 σ

lemma emod3_cast (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) : ((e : ℤ) : ZMod 3) = emod3 (fcode e) := by
  rcases (show e = -1 ∨ e = 0 ∨ e = 1 by omega) with rfl | rfl | rfl <;> decide

lemma fcode_lt (e : ℤ) : fcode e < 3 := by unfold fcode; split_ifs <;> omega

/-- `σ_c` of `lem:cert` for the tuples `t_0` (column `0`), `t_1` (column `1`) and codes `f_0, f_1`. -/
def b3sig (t0 t1 f0 f1 : ℕ) (c : Fin 2) : Fin 6 → ZMod 3 :=
  fun i => emod3 f0 * B3tupv 0 t0 i c + emod3 f1 * B3tupv 1 t1 i c

set_option maxRecDepth 100000 in
/-- **The certificate minimum** (`thm:B3`, `j = 6`): over all pairs of tuples and all steps,
`∑_c (3^6 f_6(e_c, σ_c))² ≥ 37865` (lower bounds `gapLB3`). -/
theorem b3_check : ∀ t0 : Fin 24, ∀ t1 : Fin 36, ∀ f0 f1 : Fin 3, (f0 ≠ 0 ∨ f1 ≠ 0) →
    37865 ≤ gapLB3 f0 (b3sig t0 t1 f0 f1 0) ^ 2 + gapLB3 f1 (b3sig t0 t1 f0 f1 1) ^ 2 := by
  decide +kernel

/-- The lower-bound half of `B3_cert_min`. -/
lemma B3_cert_lb (e : Fin 2 → ℤ) (l : Fin 2 → ℕ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    37865 ≤ ∑ c, gapNum (zcode 3) 6 (e c) (certSigmaP (lawD B3g B3z B3G) 6 e l c) ^ 2 := by
  obtain ⟨t0, ht0, h0⟩ := B3_resp 0 (l 0) (hl 0)
  obtain ⟨t1, ht1, h1⟩ := B3_resp 1 (l 1) (hl 1)
  have hsig : ∀ c, certSigmaP (lawD B3g B3z B3G) 6 e l c =
      b3sig t0 t1 (fcode (e 0)) (fcode (e 1)) c := by
    intro c
    funext i
    simp only [certSigmaP, b3sig, Fin.sum_univ_two]
    rw [h0 i i.isLt c, h1 i i.isLt c, emod3_cast (e 0) (he 0), emod3_cast (e 1) (he 1)]
  rewrite [Fin.sum_univ_two, hsig 0, hsig 1]
  have hne' : (⟨fcode (e 0), fcode_lt _⟩ : Fin 3) ≠ 0 ∨ (⟨fcode (e 1), fcode_lt _⟩ : Fin 3) ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    fin_cases c
    · left; intro h; apply hc; simp only [Fin.ext_iff, Fin.val_zero] at h; unfold fcode at h
      split_ifs at h with h' <;> first | exact h' | omega
    · right; intro h; apply hc; simp only [Fin.ext_iff, Fin.val_zero] at h; unfold fcode at h
      split_ifs at h with h' <;> first | exact h' | omega
  have hc := b3_check ⟨t0, ht0⟩ ⟨t1, ht1⟩ ⟨_, fcode_lt (e 0)⟩ ⟨_, fcode_lt (e 1)⟩ hne'
  exact hc.trans (Nat.add_le_add (Nat.pow_le_pow_left (gapLB3_le _ (he 0) _) 2)
    (Nat.pow_le_pow_left (gapLB3_le _ (he 1) _) 2))

set_option maxRecDepth 100000 in
lemma b3_l1 : (readV [1] (initV 0)).map acoef = B3tup0.getD 0 [] := by decide +kernel

set_option maxRecDepth 100000 in
lemma b3_l9 : (readV [0, 0, 1] (initV 1)).map acoef = B3tup1.getD 8 [] := by decide +kernel

set_option maxRecDepth 100000 in
/-- The binding case, coordinate `0` (`e_0 = 1`): the witness `R = -σ_0` gives `92 - 1 = 91`. -/
lemma b3_v0 : ((1 : ℤ) * ((3 : ℕ) : ℤ) ^ 6 +
    (encVec (zcode 3) ((fun i => 2 * b3sig 0 8 1 2 0 i) + b3sig 0 8 1 2 0) : ℤ) -
      (encVec (zcode 3) (fun i => 2 * b3sig 0 8 1 2 0 i) : ℤ)).natAbs - 1 = 91 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The binding case, coordinate `1` (`e_1 = -1`): the witness `R = 0` gives `173 - 1 = 172`. -/
lemma b3_v1 : ((-1 : ℤ) * ((3 : ℕ) : ℤ) ^ 6 +
    (encVec (zcode 3) (0 + b3sig 0 8 1 2 1) : ℤ) -
      (encVec (zcode 3) (0 : Fin 6 → ZMod 3) : ℤ)).natAbs - 1 = 172 := by decide +kernel

lemma lawD_l1 (i : ℕ) (hi : i < 6) (c : Fin 2) : lawD B3g B3z B3G i 1 c 0 = B3tupv 0 0 i c := by
  have h := vals_read [1] (by simp) (initV 0)
  rw [show Nat.ofDigits 3 [1] = 1 by norm_num [Nat.ofDigits], vals_zero, b3_l1] at h
  rw [← vals_initV 0 1 i hi c, h]; rfl

lemma lawD_l9 (i : ℕ) (hi : i < 6) (c : Fin 2) : lawD B3g B3z B3G i 9 c 1 = B3tupv 1 8 i c := by
  have h := vals_read [0, 0, 1] (by simp) (initV 1)
  rw [show Nat.ofDigits 3 [0, 0, 1] = 9 by norm_num [Nat.ofDigits], vals_zero, b3_l9] at h
  rw [← vals_initV 1 9 i hi c, h]; rfl

lemma sum_two_sq_le3 (F : Fin 2 → ℕ) (h0 : F 0 ≤ 91) (h1 : F 1 ≤ 172) :
    ∑ c, F c ^ 2 ≤ 37865 := by
  rw [Fin.sum_univ_two]
  have a := Nat.pow_le_pow_left h0 2
  have b := Nat.pow_le_pow_left h1 2
  norm_num at a b ⊢
  omega

set_option maxRecDepth 100000 in
/-- **`thm:B3`, the certificate minimum** (`lem:cert`, `q = 3`, `j = 6`; computer-assisted in the
paper): for every step `e ∈ {-1,0,1}² ∖ {0}` and all carry lengths `l_c ≥ 1`,
`∑_c (3^6 f_6(e_c, σ_c))² ≥ 37865`, and `37865 = 91² + 172²` is attained at the antidiagonal step
`e = (1, -1)` with carry lengths `l = (1, 9)`. -/
theorem B3_cert_min :
    (∀ (e : Fin 2 → ℤ) (l : Fin 2 → ℕ), (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
      (∀ c, 1 ≤ l c) →
        37865 ≤ ∑ c, gapNum (zcode 3) 6 (e c) (certSigmaP (lawD B3g B3z B3G) 6 e l c) ^ 2) ∧
    ∑ c, gapNum (zcode 3) 6 (![1, -1] c) (certSigmaP (lawD B3g B3z B3G) 6 ![1, -1] ![1, 9] c) ^ 2 =
      37865 := by
  refine ⟨B3_cert_lb, le_antisymm ?_ (B3_cert_lb _ _ (fun c => by fin_cases c <;> simp)
    ⟨0, by simp⟩ (fun c => by fin_cases c <;> simp))⟩
  have hsig : ∀ c, certSigmaP (lawD B3g B3z B3G) 6 ![1, -1] ![1, 9] c = b3sig 0 8 1 2 c := by
    intro c
    funext i
    simp only [certSigmaP, b3sig, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [lawD_l1 i i.isLt c, lawD_l9 i i.isLt c, emod3_cast 1 (by norm_num),
      emod3_cast (-1) (by norm_num)]
    rfl
  have hF0 : gapNum (zcode 3) 6 (![1, -1] 0) (certSigmaP (lawD B3g B3z B3G) 6 ![1, -1] ![1, 9] 0) ≤ 91 := by
    refine (gapNum_le (zcode 3) 6 _ _ (fun i => 2 * b3sig 0 8 1 2 0 i)).trans (le_of_eq ?_)
    rewrite [hsig 0]
    exact b3_v0
  have hF1 : gapNum (zcode 3) 6 (![1, -1] 1) (certSigmaP (lawD B3g B3z B3G) 6 ![1, -1] ![1, 9] 1) ≤ 172 := by
    refine (gapNum_le (zcode 3) 6 _ _ 0).trans (le_of_eq ?_)
    rewrite [hsig 1]
    exact b3_v1
  exact sum_two_sq_le3 _ hF0 hF1

/-! ## The level `K = 1` (`3^K < 4`): a direct check of the nine points of `P_2` -/

/-- The first six coefficients of `g_c` (from the closed form `B3_M`). -/
def b3gL (c : Fin 2) : List (ZMod 3) := (List.range 6).map (acoefN 6 (B3Mn c 0))

/-- The first six coefficients of `z_0 = τ - 1`, `z_1 = 2 - τ`. -/
def b3zL (c : Fin 2) : List (ZMod 3) :=
  ![tsub 6 (tsqrtAux 1 2 6) (tconst 6 1), tsub 6 (tconst 6 2) (tsqrtAux 1 2 6)] c

lemma b3g_rep (c : Fin 2) : TRep 6 (b3gL c) (B3g c) := by
  intro n hn
  rw [b3gL, lget_map_range _ hn, acoefN_eq 6 _ n hn, ← B3_M]
  simp [frameM]

lemma b3z_rep (c : Fin 2) : TRep 6 (b3zL c) (B3z c) := by
  have hh : (2 : ZMod 3) = (2 : ZMod 3)⁻¹ := eq_inv_of_mul_eq_one_left (by decide)
  have hs := tsqrt_rep (1 : ZMod 3) 2 hh 6
  fin_cases c
  · have h := tsub_rep hs (tconst_rep 6 (1 : ZMod 3))
    rw [map_one] at h
    exact h
  · have h := tsub_rep (tconst_rep 6 (2 : ZMod 3)) hs
    rw [map_ofNat] at h
    exact h

/-- The first six digits of the points `y(v)`, `v < 9`, as an integer (`cellIdx … 6`). -/
def b3cell6 (v : ℕ) (c : Fin 2) : ℕ :=
  ∑ n : Fin 6, (∑ k ∈ range (v + 1),
    cget (tcols 6 9 (b3gL c) (b3zL c)) k n * idxDigit (zcode 3) v k).val * 3 ^ (6 - 1 - (n : ℕ))

lemma cell6 (v : ℕ) (hv : v < 9) (c : Fin 2) : cellIdx (zcode 3) B3gen v c 6 = b3cell6 v c := by
  unfold cellIdx b3cell6
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [z3enc]
  congr 2
  unfold seqDigit
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 9 := by have := Finset.mem_range.mp hk; omega
  rw [show B3gen c n k = _ from ssGen_entry B3g B3z c (b3g_rep c) (b3z_rep c) n k n.isLt hk']

set_option maxRecDepth 100000 in
/-- Every two of the nine points of `P_2` are at least `100` six-digit cells apart in one coordinate
(on the circle of `729` cells). -/
theorem b3_cell6_far : ∀ v w : Fin 9, v ≠ w → ∃ c : Fin 2,
    100 ≤ ((b3cell6 v c : ℤ) - b3cell6 w c).natAbs ∧
      ((b3cell6 v c : ℤ) - b3cell6 w c).natAbs + 100 ≤ 729 := by
  decide +kernel

/-- **`thm:B3`, level `K = 1`**: `c(P_2) ≥ √37865/729` (every pair of the nine points has a coordinate
with toroidal gap `≥ 99/729`, so `c(P_2) ≥ 297/729 = 0.407`). -/
theorem B3_sep_one : SepAtLevel 3 2 1 (seqPoint (zcode 3) B3gen) (Real.sqrt 37865 / 729) := by
  intro v w hv hw hvw
  have hv9 : v < 9 := by simpa using hv
  have hw9 : w < 9 := by simpa using hw
  obtain ⟨c, hc1, hc2⟩ := b3_cell6_far ⟨v, hv9⟩ ⟨w, hw9⟩ (fun h => hvw (congrArg Fin.val h))
  have cv := coord_cell (by norm_num : 2 ≤ 3) (zcode 3) B3gen v c 6
  have cw := coord_cell (by norm_num : 2 ≤ 3) (zcode 3) B3gen w c 6
  rw [cell6 v hv9] at cv
  rw [cell6 w hw9] at cw
  simp only [Fin.val_mk] at hc1 hc2
  zify at hc1 hc2
  have hd1 : (100 : ℝ) ≤ |(b3cell6 v c : ℝ) - b3cell6 w c| := by exact_mod_cast hc1
  have hd2 : |(b3cell6 v c : ℝ) - b3cell6 w c| + 100 ≤ (3 : ℝ) ^ 6 := by
    norm_num; exact_mod_cast hc2
  have ht := tor_cells (Q := (3 : ℝ) ^ 6) (by positivity) (by exact_mod_cast cv.1)
    (by exact_mod_cast cv.2) (by exact_mod_cast cw.1) (by exact_mod_cast cw.2) hd1 hd2
  have hT : Z3NetDGS.torCoord (seqPoint (zcode 3) B3gen v c) (seqPoint (zcode 3) B3gen w c) ≤
      Z3NetDGS.torDist2 (seqPoint (zcode 3) B3gen v) (seqPoint (zcode 3) B3gen w) := by
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => Z3NetDGS.torCoord (seqPoint (zcode 3) B3gen v j)
      (seqPoint (zcode 3) B3gen w j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ c)
  have hs : Real.sqrt 37865 ≤ 195 := by
    rw [show (195 : ℝ) = Real.sqrt (195 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  push_cast
  norm_num at ht
  nlinarith

/-! ## `thm:B3` and `cor:allprimes` -/

lemma B3_LB_le_one : Real.sqrt 37865 / 729 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  rw [show (729 : ℝ) = Real.sqrt (729 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma B3_LB_pos : 0 < Real.sqrt 37865 / 729 := by positivity

/-- **`thm:B3`** (separation): `c(P_{2K}) ≥ √37865/729 = 0.266926…` for every `K ≥ 1`. -/
theorem B3_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 3 2 K (seqPoint (zcode 3) B3gen) (Real.sqrt 37865 / 729) := by
  rcases Nat.lt_or_ge K 2 with h | h
  · obtain rfl : K = 1 := by omega
    exact B3_sep_one
  have hK4 : 4 ≤ 3 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
  have hc := cert_prime B3gen K 6 hK4 (B3_net (2 * K) 0) (lawD B3g B3z B3G)
    (fun i _ l h1 h2 c c' => B3_law K i l h1 h2 c c') (Real.sqrt 37865 / 729) ?_
  · rwa [min_eq_right B3_LB_le_one] at hc
  rintro e l ⟨he, hne, hl⟩
  have hb := B3_cert_lb e l he hne (fun c => (hl c).1)
  rewrite [Fin.sum_univ_two] at hb
  unfold certTerm
  rewrite [Fin.sum_univ_two]
  generalize gapNum (zcode 3) 6 (e 0) (certSigmaP (lawD B3g B3z B3G) 6 e l 0) = A at hb ⊢
  generalize gapNum (zcode 3) 6 (e 1) (certSigmaP (lawD B3g B3z B3G) 6 e l 1) = B at hb ⊢
  apply Real.le_sqrt_of_sq_le
  have hb' : (37865 : ℝ) ≤ (A : ℝ) ^ 2 + (B : ℝ) ^ 2 := by exact_mod_cast hb
  rw [div_pow, Real.sq_sqrt (by norm_num), div_pow, div_pow, ← add_div]
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

/-- **`thm:B3`** (all `N`): `δ(P_{[N]}) ≥ 0.0889 · N^{-1/2}` for every `N ≥ 2`. -/
theorem B3_allN : SepAllN 2 (seqPoint (zcode 3) B3gen) (889 / 10000) := by
  have h := prefix_sep 3 2 (by norm_num) (by norm_num) (seqPoint (zcode 3) B3gen) _ B3_LB_pos.le
    (fun K hK => B3_sep K hK)
  refine sepAllN_mono _ ?_ h
  have hs : (19443 / 100 : ℝ) ≤ Real.sqrt 37865 := Real.le_sqrt_of_sq_le (by norm_num)
  push_cast
  rw [div_div, le_div_iff₀ (by norm_num)]
  nlinarith

/-- **`thm:B3`** (mesh ratio): `h(P_{[N]}) ≤ 16 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem B3_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 3) B3gen)) ≤
      16 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 3) B3gen))) := by
  have h := prefix_mesh (zcode 3) B3gen (by norm_num) (by norm_num) B3_net _ B3_LB_pos
    (fun K hK => B3_sep K hK) N hN
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h2 : Real.sqrt 2 ≤ 141422 / 100000 := by
      rw [show (141422 / 100000 : ℝ) = Real.sqrt ((141422 / 100000) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs : (19458 / 100 : ℝ) ≤ Real.sqrt 37865 := Real.le_sqrt_of_sq_le (by norm_num)
    push_cast
    rw [div_le_iff₀ B3_LB_pos]
    nlinarith
  · have : 0 ≤ Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 3) B3gen)) :=
      Real.iInf_nonneg fun _ => div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    linarith

lemma sepAtLevel_mono {q s K : ℕ} (pt : ℕ → Fin s → ℝ) {b b' : ℝ} (hb : b' ≤ b)
    (h : SepAtLevel q s K pt b) : SepAtLevel q s K pt b' :=
  fun v w hv hw hvw => hb.trans (h v w hv hw hvw)

/-- **`cor:allprimes`**: for every prime `p` there is an explicit scramble of the Faure sequence in
base `p` with algebraic multipliers in closed form that is a `(0,2)`-sequence with
`c(P_{2K}) ≥ 0.3678` (`p = 2`, `thm:B2`), `≥ 0.2669` (`p = 3`, `thm:B3`) and `≥ (p-3)/(2p)`
(`p ≥ 5`, both brick walls `W^±`, `thm:WF`) for every `K ≥ 1`. -/
theorem allprimes :
    (IsSeq0 (zcode 2) B2gen ∧
      ∀ K, 1 ≤ K → SepAtLevel 2 2 K (seqPoint (zcode 2) B2gen) (3678 / 10000)) ∧
    (IsSeq0 (zcode 3) B3gen ∧
      ∀ K, 1 ≤ K → SepAtLevel 3 2 K (seqPoint (zcode 3) B3gen) (2669 / 10000)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ a : ZMod p, (a = 1 ∨ a = -1) →
      IsSeq0 (zcode p) (WFgen p a) ∧
        ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p))) := by
  refine ⟨⟨B2_net, fun K hK => sepAtLevel_mono _ ?_ (B2_sep K hK)⟩,
    ⟨B3_net, fun K hK => sepAtLevel_mono _ ?_ (B3_sep K hK)⟩,
    fun p _ hp a ha => ⟨WF_net p hp a ha, fun K hK => WF_sep p hp a ha K hK⟩⟩
  · have hs : (15065088 / 10000 : ℝ) ≤ Real.sqrt 2269618 := Real.le_sqrt_of_sq_le (by norm_num)
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  · have hs : (1945701 / 10000 : ℝ) ≤ Real.sqrt 37865 := Real.le_sqrt_of_sq_le (by norm_num)
    rw [le_div_iff₀ (by norm_num)]; nlinarith

/-- **`cor:allprimes`** (quasi-uniform form): for every prime `p` there is an explicit `(0,2)`-sequence
in base `p` (`thm:B2`, `thm:B3`, `thm:WF`) with `c(P_{2K}) ≥ LB > 0` for all `K ≥ 1`,
`δ(P_{[N]}) ≥ b N^{-1/2}` for all `N ≥ 2`, and a bounded mesh ratio `h ≤ κ δ` along all `N`. -/
theorem allprimes_qu (p : ℕ) [hp : Fact p.Prime] :
    ∃ (C : Gen 2 (ZMod p)) (LB b κ : ℝ), 0 < LB ∧ 0 < b ∧ IsSeq0 (zcode p) C ∧
      (∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) C) LB) ∧
      SepAllN 2 (seqPoint (zcode p) C) b ∧
      ∀ N, 2 ≤ N → Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
        κ * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  have h2 := hp.out.two_le
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · left; rfl
        · right; left; rfl
        · exact absurd hp.out (by decide)
      · right; right; exact h) with rfl | rfl | h5
  · exact ⟨B2gen, _, _, _, by positivity, by norm_num, B2_net, B2_sep, B2_allN, B2_mesh⟩
  · exact ⟨B3gen, _, _, _, B3_LB_pos, by norm_num, B3_net, B3_sep, B3_allN, B3_mesh⟩
  · refine ⟨WFgen p 1, _, _, _, ?_, ?_, WF_net p h5 1 (Or.inl rfl), WF_sep p h5 1 (Or.inl rfl),
      WF_allN p h5 1 (Or.inl rfl), WF_mesh p h5 1 (Or.inl rfl)⟩
    · have : (5 : ℝ) ≤ p := by exact_mod_cast h5
      apply div_pos <;> linarith
    · have : (5 : ℝ) ≤ p := by exact_mod_cast h5
      apply div_pos <;> nlinarith

end GeoSeq
