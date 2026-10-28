/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B2Cert
public import GeoSeq.F4

@[expose] public section

/-!
# GeoSeq stage S8: `f_j` over `𝔽_4` with the binary code (`lem:cert`, `rem:F4carry`)

With the code `0, 1, ω, ω² ↦ 0, 1, 2, 3` addition in `𝔽_4` is XOR of the codes, digit by digit, so
`enc(R ⊕ σ) = enc(R) XOR enc(σ)` for digit vectors (`encVec_xor4`), and `f_j` over `𝔽_4` is the
base-2 quantity `f_{2j}` of the `2j`-bit word `enc σ`. The closed forms (lower bounds; they are the
exact minima, as in base two):
* `4^j f_j(±1, σ) ≥ 4^j - 1 - enc σ` (`gapNum4_pm`);
* `4^j f_j(0, σ) ≥ topW j (enc σ) - 1` (`gapNum4_zero`), where for the leading nonzero digit `d` of
  `σ` (position with `k` digits after it) `topW = m(d) 4^k - enc(rest)`, `m(1) = m(3) = 1`, `m(2) = 2`
  (`= 2^{t+1} - enc σ` with `2^t` the leading bit).
`topW` is computed on the natural number `enc σ`, so the certificate check runs on words.
-/

namespace GeoSeq

open Finset

/-! ## XOR of codes -/

lemma f4_digit_xor (a b : F4) :
    ((f4code.enc (a + b) : Fin 4) : ℕ) = ((f4code.enc a : Fin 4) : ℕ) ^^^ ((f4code.enc b : Fin 4) : ℕ) := by
  cases a <;> cases b <;> rfl

lemma xor_split (x y A B j : ℕ) (hA : A < 4 ^ j) (hB : B < 4 ^ j) :
    (x * 4 ^ j + A) ^^^ (y * 4 ^ j + B) = (x ^^^ y) * 4 ^ j + (A ^^^ B) := by
  have hP : (4 : ℕ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  rw [hP] at hA hB ⊢
  have hpos : 0 < 2 ^ (2 * j) := by positivity
  have d1 : (x * 2 ^ (2 * j) + A) / 2 ^ (2 * j) = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hA, zero_add]
  have d2 : (y * 2 ^ (2 * j) + B) / 2 ^ (2 * j) = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hB, zero_add]
  have m1 : (x * 2 ^ (2 * j) + A) % 2 ^ (2 * j) = A := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA]
  have m2 : (y * 2 ^ (2 * j) + B) % 2 ^ (2 * j) = B := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]
  set N := (x * 2 ^ (2 * j) + A) ^^^ (y * 2 ^ (2 * j) + B)
  have hd : N / 2 ^ (2 * j) = x ^^^ y := by rw [Nat.xor_div_two_pow, d1, d2]
  have hm : N % 2 ^ (2 * j) = A ^^^ B := by rw [Nat.xor_mod_two_pow, m1, m2]
  have := Nat.div_add_mod N (2 ^ (2 * j))
  rw [hd, hm] at this
  rw [← this]; ring

/-- `enc(a ⊕ b) = enc(a) XOR enc(b)` for digit vectors over `𝔽_4`. -/
lemma encVec_xor4 {j : ℕ} (a b : Fin j → F4) :
    encVec f4code (a + b) = encVec f4code a ^^^ encVec f4code b := by
  induction j with
  | zero => simp [encVec_zero]
  | succ j ih =>
    rw [encVec_succ, encVec_succ, encVec_succ f4code b]
    have ht : Fin.tail (a + b) = Fin.tail a + Fin.tail b := rfl
    rw [ht, ih, xor_split _ _ _ _ _ (encVec_lt f4code _) (encVec_lt f4code _)]
    rw [show (a + b) 0 = a 0 + b 0 from rfl, f4_digit_xor]

lemma encVec_zero4 {j : ℕ} : encVec f4code (0 : Fin j → F4) = 0 := by
  simp [encVec]; intro _; rfl

/-! ## Bounds for `f_j` -/

lemma f4_diff_le : ∀ a b : F4,
    |(((f4code.enc (a + b) : Fin 4) : ℕ) : ℤ) - ((f4code.enc a : Fin 4) : ℕ)| ≤
      ((f4code.enc b : Fin 4) : ℕ) := by decide

/-- `|enc(R ⊕ σ) − enc(R)| ≤ enc(σ)` over `𝔽_4`. -/
lemma enc_diff4 {j : ℕ} (r σ : Fin j → F4) :
    |(encVec f4code (r + σ) : ℤ) - encVec f4code r| ≤ encVec f4code σ := by
  induction j with
  | zero => simp [encVec_zero]
  | succ j ih =>
    rw [encVec_succ, encVec_succ, encVec_succ f4code σ]
    have ht : Fin.tail (r + σ) = Fin.tail r + Fin.tail σ := rfl
    rw [ht]
    have h0 := f4_diff_le (r 0) (σ 0)
    have hi := ih (Fin.tail r) (Fin.tail σ)
    simp only [Pi.add_apply] at h0 hi ⊢
    push_cast
    have e : (((f4code.enc (r 0 + σ 0) : Fin 4) : ℕ) : ℤ) * 4 ^ j +
        encVec f4code (Fin.tail r + Fin.tail σ) -
        (((f4code.enc (r 0) : Fin 4) : ℕ) * 4 ^ j + encVec f4code (Fin.tail r)) =
        ((((f4code.enc (r 0 + σ 0) : Fin 4) : ℕ) : ℤ) - ((f4code.enc (r 0) : Fin 4) : ℕ)) * 4 ^ j +
          ((encVec f4code (Fin.tail r + Fin.tail σ) : ℤ) - encVec f4code (Fin.tail r)) := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 4 ^ j)]
    have hp : (0 : ℤ) ≤ 4 ^ j := by positivity
    nlinarith

lemma f4_diff_ge : ∀ a b : F4, b ≠ 0 →
    (mdig ((f4code.enc b : Fin 4) : ℕ) : ℤ) ≤
      |(((f4code.enc (a + b) : Fin 4) : ℕ) : ℤ) - ((f4code.enc a : Fin 4) : ℕ)| := by decide

lemma f4_diff_zero (a : F4) :
    (((f4code.enc (a + 0) : Fin 4) : ℕ) : ℤ) - ((f4code.enc a : Fin 4) : ℕ) = 0 := by
  rw [add_zero]; ring

/-- The bound for `e = 0` on digit vectors: `m(σ_t) 4^k − enc(ρ)` for the leading nonzero digit
`σ_t` and the `k` digits `ρ` after it (`0` for `σ = 0`). -/
def topF4 : (j : ℕ) → (Fin j → F4) → ℕ
  | 0, _ => 0
  | j + 1, σ => if σ 0 = 0 then topF4 j (Fin.tail σ)
      else mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) * 4 ^ j - encVec f4code (Fin.tail σ)

lemma topF4_le {j : ℕ} (r σ : Fin j → F4) :
    (topF4 j σ : ℤ) ≤ |(encVec f4code (r + σ) : ℤ) - encVec f4code r| := by
  induction j with
  | zero => simp [topF4]
  | succ j ih =>
    rw [encVec_succ, encVec_succ]
    have ht : Fin.tail (r + σ) = Fin.tail r + Fin.tail σ := rfl
    rw [ht]
    simp only [Pi.add_apply]
    push_cast
    set B := (encVec f4code (Fin.tail r + Fin.tail σ) : ℤ) - encVec f4code (Fin.tail r)
    have e : (((f4code.enc (r 0 + σ 0) : Fin 4) : ℕ) : ℤ) * 4 ^ j +
        encVec f4code (Fin.tail r + Fin.tail σ) -
        (((f4code.enc (r 0) : Fin 4) : ℕ) * 4 ^ j + encVec f4code (Fin.tail r)) =
        ((((f4code.enc (r 0 + σ 0) : Fin 4) : ℕ) : ℤ) - ((f4code.enc (r 0) : Fin 4) : ℕ)) * 4 ^ j + B := by
      simp only [B]; ring
    rw [e]
    by_cases h0 : σ 0 = 0
    · simp only [topF4, h0, ite_true]
      rw [f4_diff_zero, zero_mul, zero_add]
      exact ih (Fin.tail r) (Fin.tail σ)
    · simp only [topF4, h0, ite_false]
      have hlt := encVec_lt f4code (Fin.tail σ)
      have hm : mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) ≤ 2 := by unfold mdig; split_ifs <;> omega
      have hd := f4_diff_ge (r 0) (σ 0) h0
      have hB := enc_diff4 (Fin.tail r) (Fin.tail σ)
      set A := ((((f4code.enc (r 0 + σ 0) : Fin 4) : ℕ) : ℤ) - ((f4code.enc (r 0) : Fin 4) : ℕ)) * 4 ^ j
      have hA : (mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) : ℤ) * 4 ^ j ≤ |A| := by
        simp only [A]; rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 4 ^ j)]
        exact mul_le_mul_of_nonneg_right hd (by positivity)
      have h := abs_add_le (A + B) (-B)
      rw [add_neg_cancel_right, abs_neg] at h
      have hsub : ((mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) * 4 ^ j -
          encVec f4code (Fin.tail σ) : ℕ) : ℤ) ≤
          (mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) : ℤ) * 4 ^ j - encVec f4code (Fin.tail σ) ∨
          (mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) * 4 ^ j - encVec f4code (Fin.tail σ) : ℕ) = 0 := by
        rcases le_total (encVec f4code (Fin.tail σ)) (mdig ((f4code.enc (σ 0) : Fin 4) : ℕ) * 4 ^ j)
          with hle | hle
        · left; rw [Nat.cast_sub hle]; push_cast; rfl
        · right; omega
      rcases hsub with hs | hs
      · linarith
      · rw [hs]; push_cast; exact abs_nonneg _

lemma topF4_eq {j : ℕ} (σ : Fin j → F4) : topF4 j σ = topW j (encVec f4code σ) := by
  induction j with
  | zero => simp [topF4, topW]
  | succ j ih =>
    rw [encVec_succ]
    have hlt := encVec_lt f4code (Fin.tail σ)
    have hpos : 0 < 4 ^ j := by positivity
    have hdiv : (((f4code.enc (σ 0) : Fin 4) : ℕ) * 4 ^ j + encVec f4code (Fin.tail σ)) / 4 ^ j =
        ((f4code.enc (σ 0) : Fin 4) : ℕ) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
    have hmod : (((f4code.enc (σ 0) : Fin 4) : ℕ) * 4 ^ j + encVec f4code (Fin.tail σ)) % 4 ^ j =
        encVec f4code (Fin.tail σ) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have hz : ∀ x : F4, x = 0 ↔ ((f4code.enc x : Fin 4) : ℕ) = 0 := by decide
    simp only [topF4, topW, hdiv, hmod]
    by_cases h0 : σ 0 = 0
    · have h0' := (hz _).mp h0
      rw [if_pos h0, if_pos h0', ih, h0', zero_mul, zero_add]
    · have h0' : ¬ ((f4code.enc (σ 0) : Fin 4) : ℕ) = 0 := fun h => h0 ((hz _).mpr h)
      rw [if_neg h0, if_neg h0']

/-- `4^j f_j(±1, σ) ≥ 4^j − 1 − enc σ` over `𝔽_4`. -/
lemma gapNum4_pm (j : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) (σ : Fin j → F4) :
    4 ^ j - encVec f4code σ - 1 ≤ gapNum f4code j e σ := by
  apply gapNum_ge
  intro r
  have hd := enc_diff4 r σ
  have hlt := encVec_lt f4code σ
  zify [hlt.le]
  rcases he with rfl | rfl
  · rw [abs_le] at hd
    rw [le_abs]; left; push_cast; linarith
  · rw [abs_le] at hd
    rw [le_abs]; right; push_cast; linarith

/-- `4^j f_j(0, σ) ≥ topW j (enc σ) − 1` over `𝔽_4`. -/
lemma gapNum4_zero (j : ℕ) (σ : Fin j → F4) :
    topW j (encVec f4code σ) - 1 ≤ gapNum f4code j 0 σ := by
  apply gapNum_ge
  intro r
  have h := topF4_le r σ
  rw [topF4_eq] at h
  zify
  simpa using h

end GeoSeq
