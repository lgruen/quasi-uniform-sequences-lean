/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B3Cert
public import GeoSeq.S3Defs

@[expose] public section

/-!
# GeoSeq stage S8: digit vectors over `𝔽_3` as words (for the certificate of `thm:S3`)

The certificate check of `thm:S3` runs on the base-3 integers `enc σ` of digit vectors. Digitwise
addition and negation in `𝔽_3` are the word functions `add3W`, `neg3W` (`encVec_add3`, `encVec_two3`),
the bound for `e = 0` of `B3Cert` is `top3W` (`top3_eqW`), and the two leading digits of a sum are the
digitwise sum of the leading digits (`add3W_div`, `neg3W_div`).
-/

namespace GeoSeq

open Finset

lemma z3_val_add (a b : ZMod 3) : (a + b).val = (a.val + b.val) % 3 := by revert a b; decide

lemma z3_val_two (a : ZMod 3) : (2 * a).val = (3 - a.val % 3) % 3 := by revert a; decide

lemma div_mod_split {d A j : ℕ} (hA : A < 3 ^ j) : (d * 3 ^ j + A) / 3 ^ j = d ∧ (d * 3 ^ j + A) % 3 ^ j = A := by
  have hpos : 0 < 3 ^ j := by positivity
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hA, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA]

/-- `enc(σ ⊕ τ) = add3W (enc σ) (enc τ)` over `𝔽_3`. -/
lemma encVec_add3 {j : ℕ} (σ τ : Fin j → ZMod 3) :
    encVec (zcode 3) (σ + τ) = add3W j (encVec (zcode 3) σ) (encVec (zcode 3) τ) := by
  induction j with
  | zero => simp [encVec_zero, add3W]
  | succ j ih =>
    rw [encVec_succ, encVec_succ (zcode 3) σ, encVec_succ (zcode 3) τ]
    obtain ⟨h1, h2⟩ := div_mod_split (d := ((zcode 3).enc (σ 0) : ℕ)) (encVec_lt (zcode 3) (Fin.tail σ))
    obtain ⟨h3, h4⟩ := div_mod_split (d := ((zcode 3).enc (τ 0) : ℕ)) (encVec_lt (zcode 3) (Fin.tail τ))
    simp only [add3W, h1, h2, h3, h4]
    have ht : Fin.tail (σ + τ) = Fin.tail σ + Fin.tail τ := rfl
    rw [ht, ih, show (σ + τ) 0 = σ 0 + τ 0 from rfl, z3enc, z3enc, z3enc, z3_val_add]

/-- `enc(-σ) = enc(2σ) = neg3W (enc σ)` over `𝔽_3`. -/
lemma encVec_two3 {j : ℕ} (σ : Fin j → ZMod 3) :
    encVec (zcode 3) (fun i => 2 * σ i) = neg3W j (encVec (zcode 3) σ) := by
  induction j with
  | zero => simp [encVec_zero, neg3W]
  | succ j ih =>
    rw [encVec_succ, encVec_succ (zcode 3) σ]
    obtain ⟨h1, h2⟩ := div_mod_split (d := ((zcode 3).enc (σ 0) : ℕ)) (encVec_lt (zcode 3) (Fin.tail σ))
    simp only [neg3W, h1, h2]
    have ht : Fin.tail (fun i => 2 * σ i) = fun i => 2 * Fin.tail σ i := rfl
    rw [ht, ih, z3enc, z3enc, z3_val_two]

lemma top3_eqW {j : ℕ} (σ : Fin j → ZMod 3) : top3 j σ = top3W j (encVec (zcode 3) σ) := by
  induction j with
  | zero => simp [top3, top3W]
  | succ j ih =>
    rw [encVec_succ]
    obtain ⟨h1, h2⟩ := div_mod_split (d := ((zcode 3).enc (σ 0) : ℕ)) (encVec_lt (zcode 3) (Fin.tail σ))
    simp only [top3, top3W]
    rw [h1, h2, ← encVec_two3, ← ih]
    have e0 : ∀ x : ZMod 3, (((zcode 3).enc x : ℕ) % 3 = 0 ↔ x = 0) := by decide
    have e1 : ∀ x : ZMod 3, (((zcode 3).enc x : ℕ) % 3 = 1 ↔ x = 1) := by decide
    by_cases h0 : σ 0 = 0
    · rw [if_pos h0, if_pos ((e0 _).mpr h0)]
    · rw [if_neg h0, if_neg (fun h => h0 ((e0 _).mp h))]
      by_cases h1' : σ 0 = 1
      · rw [if_pos h1', if_pos ((e1 _).mpr h1')]
      · rw [if_neg h1', if_neg (fun h => h1' ((e1 _).mp h))]

lemma encVec_zero3 {j : ℕ} : encVec (zcode 3) (fun _ : Fin j => (0 : ZMod 3)) = 0 := by
  simp [encVec, z3enc]

lemma add3W_lt (j a b : ℕ) : add3W j a b < 3 ^ j := by
  induction j generalizing a b with
  | zero => simp [add3W]
  | succ j ih =>
    simp only [add3W]
    have := ih (a % 3 ^ j) (b % 3 ^ j)
    have h3 : (a / 3 ^ j + b / 3 ^ j) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rw [pow_succ]; nlinarith

lemma neg3W_lt (j a : ℕ) : neg3W j a < 3 ^ j := by
  induction j generalizing a with
  | zero => simp [neg3W]
  | succ j ih =>
    simp only [neg3W]
    have := ih (a % 3 ^ j)
    have h3 : (3 - a / 3 ^ j % 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rw [pow_succ]; nlinarith

lemma div_pow_split (a n k : ℕ) : a / 3 ^ k / 3 ^ n = a / 3 ^ (n + k) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm k n]

lemma mod_pow_split (a n k : ℕ) : a % 3 ^ (n + k) / 3 ^ k = a / 3 ^ k % 3 ^ n := by
  rw [show 3 ^ (n + k) = 3 ^ k * 3 ^ n by rw [← pow_add, Nat.add_comm], Nat.mod_mul_right_div_self]

/-- The leading `n` digits of a digitwise sum are the digitwise sum of the leading digits. -/
lemma add3W_div (n k a b : ℕ) : add3W (n + k) a b / 3 ^ k = add3W n (a / 3 ^ k) (b / 3 ^ k) := by
  induction n generalizing a b with
  | zero =>
    rw [zero_add, Nat.div_eq_of_lt (add3W_lt k a b)]; rfl
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [add3W]
    have hpos : 0 < 3 ^ k := by positivity
    rw [show ((a / 3 ^ (n + k) + b / 3 ^ (n + k)) % 3) * 3 ^ (n + k) =
        ((a / 3 ^ (n + k) + b / 3 ^ (n + k)) % 3 * 3 ^ n) * 3 ^ k by rw [pow_add]; ring,
      Nat.add_comm, Nat.add_mul_div_right _ _ hpos, ih, mod_pow_split, mod_pow_split,
      div_pow_split, div_pow_split, Nat.add_comm]

lemma neg3W_div (n k a : ℕ) : neg3W (n + k) a / 3 ^ k = neg3W n (a / 3 ^ k) := by
  induction n generalizing a with
  | zero =>
    rw [zero_add, Nat.div_eq_of_lt (neg3W_lt k a)]; rfl
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [neg3W]
    have hpos : 0 < 3 ^ k := by positivity
    rw [show ((3 - a / 3 ^ (n + k) % 3) % 3) * 3 ^ (n + k) =
        ((3 - a / 3 ^ (n + k) % 3) % 3 * 3 ^ n) * 3 ^ k by rw [pow_add]; ring,
      Nat.add_comm, Nat.add_mul_div_right _ _ hpos, ih, mod_pow_split, div_pow_split, Nat.add_comm]

/-- Solving for the leading digits of the third summand (finite check over two digits). -/
lemma add3W_solve : ∀ x y : Fin 9, ∀ T : Fin 9, add3W 2 x y = T → (y : ℕ) = add3W 2 T (neg3W 2 x) := by
  decide

lemma neg3W_key : ∀ x : Fin 9, (x : ℕ) ≠ 4 → neg3W 2 x ≠ 8 := by decide

end GeoSeq
