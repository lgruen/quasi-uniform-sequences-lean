/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SteerDefs
public import GeoSeq.WFSep

@[expose] public section

/-!
# GeoSeq stage S7: the window certificate (`thm:GA`, certificate part; `lem:dom`)

* `f1_one_val`, `f1_zero_val`: `f_1(1, σ) = ((σ = 0 ? p : val σ) - 1)/p`, `f_1(0, σ) = (min(val σ, p - val σ) - 1)/p`
  (`rem:onedigit`); `F0_neg`: `f_1(0, -σ) = f_1(0, σ)`.
* `f1_int_nonpos`, `f1_int_pos`, `f0_int`: the same for integer representatives.
* **`win_cert`**: for a `(0,2)`-sequence over `𝔽_p`, `p ≥ 5`, whose one-digit responses lie in windows,
  `c(P_{2K}) ≥ min(1, LB)` for every `K ≥ 1` whenever `LB` is below the four numbers of `thm:GA`
  (the certificate half of the proof of `thm:GA`; `lem:cert`, `j = 1`, steps up to sign).
* **`dom`** (`lem:dom`): interval windows `O ∈ [-A,-B]`, `X ∈ [-B,B]`.
-/

namespace GeoSeq

open Finset

/-- `f_1(1, σ)`: numerator `(σ = 0 ? p : val σ) - 1`. -/
theorem f1_one_val (p : ℕ) [NeZero p] (σ : ZMod p) :
    gapNum1 p 1 σ = (if σ = 0 then p else σ.val) - 1 := by
  by_cases h : σ = 0
  · subst h; simp [gapNum1_zero]
  · rw [gapNum1_eq p 1 σ h, if_neg h]
    have := ZMod.val_lt σ
    congr 1
    omega

/-- `f_1(0, σ)`: numerator `min(val σ, p - val σ) - 1`. -/
theorem f1_zero_val (p : ℕ) [NeZero p] (σ : ZMod p) :
    gapNum1 p 0 σ = min σ.val (p - σ.val) - 1 := by
  by_cases h : σ = 0
  · subst h; simp [gapNum1_zero]
  · rw [gapNum1_eq p 0 σ h]
    have := ZMod.val_lt σ
    congr 1
    omega

/-- `f_1(0, -σ) = f_1(0, σ)`. -/
theorem F0_neg (p : ℕ) [NeZero p] (σ : ZMod p) : gapNum1 p 0 (-σ) = gapNum1 p 0 σ := by
  rw [f1_zero_val, f1_zero_val, ZMod.neg_val]
  have := ZMod.val_lt σ
  split_ifs with h
  · subst h; simp
  · congr 1; omega

lemma val_intCast_of (p : ℕ) [NeZero p] (z : ℤ) (h0 : 0 ≤ z) (h1 : z < p) :
    ((z : ZMod p).val : ℤ) = z := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h0 h1]

/-- `f_1(1, z)` for an integer `-p < z ≤ 0`: numerator `p - 1 + z`. -/
theorem f1_int_nonpos (p : ℕ) [NeZero p] (z : ℤ) (h0 : -(p : ℤ) < z) (h1 : z ≤ 0) :
    (gapNum1 p 1 (z : ZMod p) : ℤ) = p - 1 + z := by
  rw [f1_one_val]
  by_cases hz : z = 0
  · subst hz
    have : 1 ≤ p := NeZero.one_le
    simp; omega
  · have hne : (z : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      obtain ⟨c, hc⟩ := h
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; omega
      · nlinarith
    rw [if_neg hne]
    have hv : (((z + p : ℤ) : ZMod p).val : ℤ) = z + p := val_intCast_of p _ (by omega) (by omega)
    have he : ((z + p : ℤ) : ZMod p) = (z : ZMod p) := by push_cast; simp
    rw [he] at hv
    have : 1 ≤ (z : ZMod p).val := by
      rcases Nat.eq_zero_or_pos (z : ZMod p).val with h | h
      · rw [ZMod.val_eq_zero] at h; exact absurd h hne
      · exact h
    omega

/-- `f_1(1, z)` for an integer `1 ≤ z ≤ p - 1`: numerator `z - 1`. -/
theorem f1_int_pos (p : ℕ) [NeZero p] (z : ℤ) (h0 : 1 ≤ z) (h1 : z < p) :
    (gapNum1 p 1 (z : ZMod p) : ℤ) = z - 1 := by
  rw [f1_one_val]
  have hv := val_intCast_of p z (by omega) h1
  have hne : (z : ZMod p) ≠ 0 := by
    intro h; rw [h, ZMod.val_zero] at hv; omega
  rw [if_neg hne]
  omega

/-- `f_1(0, z)` for an integer `0 ≤ z ≤ p - 1`: numerator `min(z, p - z) - 1`. -/
theorem f0_int (p : ℕ) [NeZero p] (z : ℤ) (h0 : 0 ≤ z) (h1 : z < p) :
    gapNum1 p 0 (z : ZMod p) = min z.toNat (p - z.toNat) - 1 := by
  rw [f1_zero_val]
  have hv := val_intCast_of p z h0 h1
  have : (z : ZMod p).val = z.toNat := by omega
  rw [this]

/-! ## The window certificate -/

/-- **`thm:GA`, certificate part** (with `lem:cert`, `j = 1`): a `(0,2)`-sequence over `𝔽_p`,
`p ≥ 5`, whose one-digit responses lie in the windows `Wo`, `Wx` at every level, has
`c(P_{2K}) ≥ min(1, LB)` for every `K ≥ 1`, for every `LB` below the four numbers of `thm:GA`. -/
theorem win_cert (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (C : Gen 2 (ZMod p))
    (hseq : IsSeq0 (zcode p) C) (Wo Wx : Fin 2 → Set (ZMod p)) (hW : RespIn C Wo Wx) (LB : ℝ)
    (hLB : GAbound p Wo Wx LB) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) C) (min 1 LB) := by
  have hnet : BlockNet0 (zcode p) C (2 * K) 0 := hseq (2 * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  classical
  let Dr : ℕ → Fin 2 → Fin 2 → ZMod p := fun l c c' =>
    if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists (zcode p) C K hnet 0 l c c')
    else 0
  have hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c') := by
    intro l h1 h2 c c'
    simp only [Dr, And.intro h1 h2, and_self, dite_true]
    exact Classical.choose_spec (carry_exists (zcode p) C K hnet 0 l c c')
  refine cert_one C K hq hnet Dr hD LB ?_
  rintro e l ⟨he, hne, hl⟩
  obtain ⟨o0, ho0⟩ : ∃ o, o ∈ Wo 0 ∧ Dr (l 0) 0 0 = o :=
    ⟨_, (hW K (l 0) (hl 0).1 (hl 0).2 _).1 (hD _ (hl 0).1 (hl 0).2 0 0), rfl⟩
  obtain ⟨x0, hx0⟩ : ∃ x, x ∈ Wx 0 ∧ Dr (l 0) 1 0 = x :=
    ⟨_, (hW K (l 0) (hl 0).1 (hl 0).2 _).2.1 (hD _ (hl 0).1 (hl 0).2 1 0), rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ o, o ∈ Wo 1 ∧ Dr (l 1) 1 1 = o :=
    ⟨_, (hW K (l 1) (hl 1).1 (hl 1).2 _).2.2.1 (hD _ (hl 1).1 (hl 1).2 1 1), rfl⟩
  obtain ⟨x1, hx1⟩ : ∃ x, x ∈ Wx 1 ∧ Dr (l 1) 0 1 = x :=
    ⟨_, (hW K (l 1) (hl 1).1 (hl 1).2 _).2.2.2 (hD _ (hl 1).1 (hl 1).2 0 1), rfl⟩
  obtain ⟨hA0, hA1, hA2, hA3⟩ := hLB
  simp only [Fin.sum_univ_two, ho0.2, hx0.2, ho1.2, hx1.2]
  have he0 : e 0 = -1 ∨ e 0 = 0 ∨ e 0 = 1 := by have := he 0; omega
  have he1 : e 1 = -1 ∨ e 1 = 0 ∨ e 1 = 1 := by have := he 1; omega
  have hne' : e 0 ≠ 0 ∨ e 1 ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    fin_cases c
    · exact Or.inl hc
    · exact Or.inr hc
  rcases he0 with e0 | e0 | e0 <;> rcases he1 with e1 | e1 | e1 <;>
  simp only [e0, e1, Int.cast_neg, Int.cast_one, Int.cast_zero, neg_one_mul, one_mul, zero_mul,
    add_zero, zero_add, F1_neg] at hne' ⊢
  · -- e = (-1, -1)
    have := hA2 o0 ho0.1 x1 hx1.1 o1 ho1.1 x0 hx0.1
    convert this using 5 <;> ring_nf
  · -- e = (-1, 0)
    have := hA0 o0 ho0.1 x0 hx0.1
    rw [neg_neg, F0_neg]; exact this
  · -- e = (-1, 1)
    have := hA3 o0 ho0.1 x1 hx1.1 o1 ho1.1 x0 hx0.1
    convert this using 5 <;> ring_nf
  · -- e = (0, -1)
    have := hA1 o1 ho1.1 x1 hx1.1
    rw [neg_neg, F0_neg, add_comm]; exact this
  · exact absurd rfl (hne'.elim id id)
  · -- e = (0, 1)
    have := hA1 o1 ho1.1 x1 hx1.1
    rw [add_comm]; exact this
  · -- e = (1, -1)
    have := hA3 o0 ho0.1 x1 hx1.1 o1 ho1.1 x0 hx0.1
    convert this using 5 <;> ring_nf
  · -- e = (1, 0)
    exact hA0 o0 ho0.1 x0 hx0.1
  · -- e = (1, 1)
    have := hA2 o0 ho0.1 x1 hx1.1 o1 ho1.1 x0 hx0.1
    convert this using 5 <;> ring_nf

/-! ## Interval windows and `lem:dom` -/

lemma le_sqrt_left (m a b : ℝ) (h : m ≤ a) : m ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
  h.trans ((le_abs_self a).trans (Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))))

lemma le_sqrt_right (m a b : ℝ) (h : m ≤ b) : m ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [add_comm]; exact le_sqrt_left m b a h

lemma sqrt_two_le (m a b : ℝ) (hm : 0 ≤ m) (ha : m ≤ a) (hb : m ≤ b) :
    Real.sqrt 2 * m ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_sq hm, ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  nlinarith

/-- `f_1(1, z) ≥ (p - 1 - A)/p` for an integer `-A ≤ z ≤ 0`, `A < p` (real form). -/
lemma f1R_ge (p : ℕ) [NeZero p] (A : ℕ) (hA : A < p) (z : ℤ) (h0 : -(A : ℤ) ≤ z) (h1 : z ≤ 0) :
    1 - ((A : ℝ) + 1) / p ≤ (gapNum1 p 1 (z : ZMod p) : ℝ) / p := by
  have h := f1_int_nonpos p z (by omega) h1
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hR : ((gapNum1 p 1 (z : ZMod p) : ℤ) : ℝ) = (p : ℝ) - 1 + z := by rw [h]; push_cast; ring
  have hz : -(A : ℝ) ≤ z := by exact_mod_cast h0
  rw [show ((gapNum1 p 1 (z : ZMod p) : ℕ) : ℝ) = ((gapNum1 p 1 (z : ZMod p) : ℤ) : ℝ) by
    push_cast; rfl, hR, one_sub_div hp.ne', div_le_div_iff_of_pos_right hp]
  linarith

/-- **`lem:dom`** (window dominance): if every own response lies in `[-A, -B]` and every cross response in
`[-B, B]` (`0 ≤ B ≤ A`, `A + B < p`), then `c(P_{2K}) ≥ min(1 - (A+1)/p, √2 (1 - (A+B+1)/p))` for every
`K ≥ 1`. -/
theorem dom (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (C : Gen 2 (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (A B : ℕ) (hBA : B ≤ A) (hAB : A + B < p)
    (hW : RespIn C (fun _ => intWin p (-(A : ℤ)) (-(B : ℤ))) (fun _ => intWin p (-(B : ℤ)) B))
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) C)
      (min (1 - ((A : ℝ) + 1) / p) (Real.sqrt 2 * (1 - ((A : ℝ) + B + 1) / p))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set LB := min (1 - ((A : ℝ) + 1) / p) (Real.sqrt 2 * (1 - ((A : ℝ) + B + 1) / p)) with hLBdef
  have hLB1 : LB ≤ 1 := (min_le_left _ _).trans (by
    have : 0 ≤ ((A : ℝ) + 1) / p := by positivity
    linarith)
  have hm : 0 ≤ 1 - ((A : ℝ) + B + 1) / p := by
    rw [sub_nonneg, div_le_one hp0]; exact_mod_cast (show A + B + 1 ≤ p by omega)
  have h := win_cert p hp C hseq _ _ hW LB ?_ K hK
  · rwa [min_eq_right hLB1] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro o ⟨z, hz0, hz1, rfl⟩ x -
    exact (min_le_left _ _).trans (le_sqrt_left _ _ _ (f1R_ge p A (by omega) z hz0 (by omega)))
  · rintro o ⟨z, hz0, hz1, rfl⟩ x -
    exact (min_le_left _ _).trans (le_sqrt_left _ _ _ (f1R_ge p A (by omega) z hz0 (by omega)))
  · rintro o0 ⟨z0, h00, h01, rfl⟩ x1 ⟨w1, h10, h11, rfl⟩ o1 ⟨z1, h20, h21, rfl⟩ x0 ⟨w0, h30, h31, rfl⟩
    refine (min_le_right _ _).trans (sqrt_two_le _ _ _ hm ?_ ?_)
    · rw [← Int.cast_add]
      exact_mod_cast f1R_ge p (A + B) hAB _ (by push_cast; omega) (by omega)
    · rw [← Int.cast_add]
      exact_mod_cast f1R_ge p (A + B) hAB _ (by push_cast; omega) (by omega)
  · rintro o0 ⟨z0, h00, h01, rfl⟩ x1 ⟨w1, h10, h11, rfl⟩ o1 ⟨z1, h20, h21, rfl⟩ x0 ⟨w0, h30, h31, rfl⟩
    refine (min_le_right _ _).trans (sqrt_two_le _ _ _ hm ?_ ?_)
    · rw [← Int.cast_sub]
      exact_mod_cast f1R_ge p (A + B) hAB _ (by push_cast; omega) (by omega)
    · rw [← Int.cast_sub]
      exact_mod_cast f1R_ge p (A + B) hAB _ (by push_cast; omega) (by omega)

end GeoSeq
