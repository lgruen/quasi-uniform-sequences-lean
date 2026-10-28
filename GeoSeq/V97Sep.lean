/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V97Corr

@[expose] public section

/-!
# GeoSeq stage V9-7 (part 2): skeleton relations with bounded corrections (`thm:corrected`)

* `coord_step`: two fine cells whose difference `a` (centred modulo `p^K`) has `|a| < p` differ in the last digit by
  `a` and in the coarse digits by a carry `ε ∈ {-1, 0, 1}` of some length `j` (`ε = sgn a` if `ε ≠ 0`).
* `ljitB_le`, `ljitB_ge` (`ℓ_jit^{(B)} ≥ ℓ_jit - B√s`).
* **`corrected`**, `corrected_sepAtPrefix` (**`thm:corrected`**): a digital `(0,s)`-sequence over `𝔽_p` whose prefix
  `P_{sK-1}` satisfies the corrected skeleton relation, with partial sums `Ψ_c(j)` represented by integers in `[0, B]`,
  has `sep(P_{sK-1}) ≥ p^{-1/s} ℓ_jit^{(B)}(Λ_v)`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

lemma corr_sum_diff {R : Type*} [CommRing R] (K j : ℕ) (χ y x : ℕ → R) (ε : R)
    (hε : ε = 0 ∨ (1 ≤ j ∧ j ≤ K - 1))
    (h : ∀ d, 1 ≤ d → d ≤ K - 1 → y d - x d = ε * (if d ≤ j then 1 else 0)) :
    (∑ d ∈ Finset.Ico 1 K, χ d * y d) - ∑ d ∈ Finset.Ico 1 K, χ d * x d =
      ε * ∑ d ∈ Finset.Ico 1 (j + 1), χ d := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun d hd => by
    rw [← mul_sub, h d (Finset.mem_Ico.mp hd).1 (by have := Finset.mem_Ico.mp hd; omega)]]
  rcases hε with h0 | ⟨hj1, hj2⟩
  · simp [h0]
  · rw [Finset.mul_sum, ← Finset.sum_subset (Finset.Ico_subset_Ico_right (show j + 1 ≤ K by omega))
      (fun d hd hnd => by
        rw [if_neg (by simp only [Finset.mem_Ico] at hd hnd; omega), mul_zero, mul_zero])]
    exact Finset.sum_congr rfl fun d hd => by
      rw [if_pos (by simp only [Finset.mem_Ico] at hd; omega)]; ring

lemma comb_sub {R : Type*} [CommRing R] (A B S T a e : R) (h1 : A - B = a) (h2 : S - T = e) :
    (A + S) - (B + T) = a + e := by rw [← h1, ← h2]; ring

lemma sum_mul_sub_eq_zero {ι R : Type*} [CommRing R] (t : Finset ι) (v Y X : ι → R)
    (hY : ∑ i ∈ t, v i * Y i = 0) (hX : ∑ i ∈ t, v i * X i = 0) : ∑ i ∈ t, v i * (Y i - X i) = 0 := by
  simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, hY, hX, sub_zero]

lemma digInc_one (y : ZMod p) : digInc (zcode p) y = 1 := digInc_zcode p y

/-- **One coordinate of `thm:corrected`**: if the centred difference `a` of the fine cells of two points satisfies
`|a| < p`, the last digit changes by `a` and the coarse digits by a carry `ε` of length `j`. -/
theorem coord_step (C : Gen s (ZMod p)) (x y : ℕ) (c : Fin s) (K : ℕ) (hK : 1 ≤ K)
    (hap : |cenRep (p ^ K) ((cellIdx (zcode p) C y c K : ℤ) - cellIdx (zcode p) C x c K)| < p) :
    seqDigit (zcode p) C y c (K - 1) - seqDigit (zcode p) C x c (K - 1) =
        ((cenRep (p ^ K) ((cellIdx (zcode p) C y c K : ℤ) - cellIdx (zcode p) C x c K) : ℤ) : ZMod p) ∧
      ∃ ε : ℤ, ∃ j : ℕ, (ε = 0 ∨ ((ε = 1 ∨ ε = -1) ∧
        0 < ε * cenRep (p ^ K) ((cellIdx (zcode p) C y c K : ℤ) - cellIdx (zcode p) C x c K) ∧
          1 ≤ j ∧ j ≤ K - 1)) ∧
        ∀ d, 1 ≤ d → d ≤ K - 1 → seqDigit (zcode p) C y c (K - 1 - d) - seqDigit (zcode p) C x c (K - 1 - d) =
          (ε : ZMod p) * (if d ≤ j then 1 else 0) := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set a := cenRep (p ^ (K' + 1)) ((cellIdx (zcode p) C y c (K' + 1) : ℤ) - cellIdx (zcode p) C x c (K' + 1))
    with ha
  obtain ⟨t, ht⟩ := cenRep_modEq (p ^ (K' + 1))
    ((cellIdx (zcode p) C y c (K' + 1) : ℤ) - cellIdx (zcode p) C x c (K' + 1))
  rw [← ha] at ht
  -- the last digit
  have h1 : seqDigit (zcode p) C y c K' - seqDigit (zcode p) C x c K' = (a : ZMod p) := by
    rw [← cast_cellIdx, ← cast_cellIdx, ht]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
  refine ⟨h1, ?_⟩
  rcases Nat.eq_zero_or_pos K' with hK0 | hK0
  · exact ⟨0, 0, Or.inl rfl, fun d hd1 hd2 => by omega⟩
  set P := p ^ K' with hP
  have hPpos : 0 < P := pow_pos (by omega) _
  set u := cellIdx (zcode p) C x c K'
  set u' := cellIdx (zcode p) C y c K'
  set r := (seqDigit (zcode p) C x c K').val
  set r' := (seqDigit (zcode p) C y c K').val
  have hn : cellIdx (zcode p) C x c (K' + 1) = u * p + r := cellIdx_succ _ _ _ _ _
  have hm : cellIdx (zcode p) C y c (K' + 1) = u' * p + r' := cellIdx_succ _ _ _ _ _
  have hu : u < P := cellIdx_lt _ _ _ _ _
  have hu' : u' < P := cellIdx_lt _ _ _ _ _
  have hr : r < p := ZMod.val_lt _
  have hr' : r' < p := ZMod.val_lt _
  have hQ : ((p ^ (K' + 1) : ℕ) : ℤ) = (P : ℤ) * p := by rw [hP]; push_cast; ring
  rw [hn, hm, hQ] at ht
  push_cast at ht
  -- `u' p + r' = u p + r + a - t P p`
  have hap' : |a| < p := hap
  rw [abs_lt] at hap'
  have hcoarse : ∀ ε : ℤ, 0 ≤ (r : ℤ) + a - ε * p → (r : ℤ) + a - ε * p < p →
      (u' : ℤ) = u + ε - t * P := by
    intro ε h0 h1
    have : (p : ℤ) * ((u' : ℤ) - u - ε + t * P) = (r : ℤ) + a - ε * p - r' := by linear_combination -ht
    have hlt : |(r : ℤ) + a - ε * p - r'| < p := by rw [abs_lt]; constructor <;> omega
    have hz : (u' : ℤ) - u - ε + t * P = 0 := by
      by_contra hne
      have := Int.le_of_dvd (abs_pos.mpr (by rw [← this]; exact mul_ne_zero (by omega) hne))
        ((dvd_abs _ _).mpr ⟨_, this.symm⟩)
      omega
    linarith
  -- the carry digits
  have hdig : ∀ (X Z : ℕ → ZMod p), (∑ n : Fin K', ((zcode p).enc (Z n) : ℕ) * p ^ (K' - 1 - (n : ℕ)) =
      (∑ n : Fin K', ((zcode p).enc (X n) : ℕ) * p ^ (K' - 1 - (n : ℕ)) + 1) % p ^ K') →
      ∃ l, 1 ≤ l ∧ l ≤ K' ∧ ∀ d, 1 ≤ d → d ≤ K' → Z (K' - d) - X (K' - d) = if d ≤ l then 1 else 0 := by
    intro X Z hc
    obtain ⟨l, hl1, hl2, hl⟩ := carry_digits (zcode p) hp K' hK0 X Z hc
    refine ⟨l, hl1, hl2, fun d hd1 hd2 => ?_⟩
    rw [hl (K' - d) (by omega), digInc_one, digInc_one, one_mul, one_mul]
    by_cases hdl : d ≤ l
    · rw [if_pos hdl]
      by_cases hdl' : d = l
      · rw [if_neg (by omega), if_pos (by omega)]; ring
      · rw [if_pos (by omega), if_neg (by omega)]; ring
    · rw [if_neg hdl, if_neg (by omega), if_neg (by omega)]; ring
  by_cases hw0 : (r : ℤ) + a < 0
  · -- `ε = -1`
    have hc := hcoarse (-1) (by omega) (by omega)
    have hmod : u = (u' + 1) % P := by
      have h2 : ((u' + 1 : ℕ) : ℤ) = u + (-t) * P := by push_cast; linarith
      have h3 : ((u' + 1) % P : ℕ) = ((u + (-t) * P) % P : ℤ) := by rw [Int.natCast_mod, h2]
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)] at h3
      exact_mod_cast h3.symm
    obtain ⟨l, hl1, hl2, hl⟩ := hdig (fun n => seqDigit (zcode p) C y c n) (fun n => seqDigit (zcode p) C x c n)
      hmod
    refine ⟨-1, l, Or.inr ⟨Or.inr rfl, by omega, hl1, hl2⟩, fun d hd1 hd2 => ?_⟩
    have h := hl d hd1 hd2
    push_cast
    linear_combination -h
  · by_cases hwp : (p : ℤ) ≤ (r : ℤ) + a
    · -- `ε = 1`
      have hc := hcoarse 1 (by omega) (by omega)
      have hmod : u' = (u + 1) % P := by
        have h2 : ((u + 1 : ℕ) : ℤ) = u' + t * P := by push_cast; linarith
        have h3 : ((u + 1) % P : ℕ) = ((u' + t * P) % P : ℤ) := by rw [Int.natCast_mod, h2]
        rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)] at h3
        exact_mod_cast h3.symm
      obtain ⟨l, hl1, hl2, hl⟩ := hdig (fun n => seqDigit (zcode p) C x c n)
        (fun n => seqDigit (zcode p) C y c n) hmod
      refine ⟨1, l, Or.inr ⟨Or.inl rfl, by omega, hl1, hl2⟩, fun d hd1 hd2 => ?_⟩
      rw [hl d hd1 hd2]; push_cast; ring
    · -- `ε = 0`
      have hc := hcoarse 0 (by omega) (by omega)
      have heq : u' = u := by
        have : (u' : ℤ) = u - t * P := by linarith
        have hPz : (0 : ℤ) < P := by exact_mod_cast hPpos
        have hu1 : (u : ℤ) < P := by exact_mod_cast hu
        have hu2 : (u' : ℤ) < P := by exact_mod_cast hu'
        have ht0 : t = 0 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have h1 : t ≤ -1 := by omega
            nlinarith
          · have h1 : 1 ≤ t := by omega
            nlinarith
        rw [ht0] at this; omega
      refine ⟨0, 0, Or.inl rfl, fun d hd1 hd2 => ?_⟩
      have h := cell_digit (zcode p) C y c K' (K' - d) (by omega)
      have h' := cell_digit (zcode p) C x c K' (K' - d) (by omega)
      have : seqDigit (zcode p) C y c (K' - d) = seqDigit (zcode p) C x c (K' - d) := by
        apply (zcode p).enc.injective; apply Fin.ext
        rw [h, h']; congr 2
      rw [this, sub_self]; simp

lemma jitNormB_nonneg (B : ℕ) (b : Fin s → ℤ) : 0 ≤ jitNormB B b := Real.sqrt_nonneg _

omit [Fact p.Prime] in
lemma ljitB_le (B : ℕ) (v : Fin s → ZMod p) (b : Fin s → ℤ) (hb : b ≠ 0) (hlat : InLat v b) :
    ljitB B v ≤ jitNormB B b := by
  unfold ljitB
  have hbdd : BddBelow (Set.range fun b : {b : Fin s → ℤ // b ≠ 0 ∧ InLat v b} => jitNormB B b.1) :=
    ⟨0, by rintro _ ⟨b, rfl⟩; exact Real.sqrt_nonneg _⟩
  exact ciInf_le hbdd ⟨b, hb, hlat⟩

/-- `ℓ_jit^{(B)}(Λ_v) ≥ ℓ_jit(Λ_v) - B √s` (`thm:corrected`): `(|b| - 𝟏)_+ ≤ (|b| - (1+B)𝟏)_+ + B 𝟏` coordinatewise,
and the triangle inequality. -/
theorem ljitB_ge (hs : 1 ≤ s) (B : ℕ) (v : Fin s → ZMod p) : ljit v - B * Real.sqrt s ≤ ljitB B v := by
  unfold ljitB
  set c0 : Fin s := ⟨0, by omega⟩
  have hne : Nonempty {b : Fin s → ℤ // b ≠ 0 ∧ InLat v b} := by
    refine ⟨⟨fun c => if c = c0 then (p : ℤ) else 0, fun h => ?_, ?_⟩⟩
    · have := congrFun h c0
      simp only [↓reduceIte, Pi.zero_apply, Nat.cast_eq_zero] at this
      exact (Fact.out : p.Prime).ne_zero this
    · unfold InLat
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases h : c = c0 <;> simp [h]
  refine le_ciInf fun b => ?_
  rw [sub_le_iff_le_add]
  refine (ljit_le v b.1 b.2.1 b.2.2).trans ?_
  unfold jitNorm jitNormB
  set f : Fin s → ℝ := fun c => max (|(b.1 c : ℝ)| - 1 - B) 0
  have hle : ∀ c, max (|(b.1 c : ℝ)| - 1) 0 ≤ f c + B := fun c => by
    simp only [f]; rcases le_total (|(b.1 c : ℝ)| - 1 - B) 0 with h | h
    · rw [max_eq_right h]; exact max_le (by linarith) (by positivity)
    · rw [max_eq_left h]; exact max_le (by linarith) (by positivity)
  have hf0 : ∀ c, 0 ≤ f c := fun c => le_max_right _ _
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set S2 := ∑ c, f c ^ 2 with hS2
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  -- Cauchy–Schwarz: `∑ f ≤ √s √(∑ f²)`
  have hcs : (∑ c, f c) ^ 2 ≤ S2 * s := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ f (fun _ => (1 : ℝ))
    simpa [hS2] using this
  have hsum0 : 0 ≤ ∑ c, f c := Finset.sum_nonneg fun c _ => hf0 c
  have hcs' : ∑ c, f c ≤ Real.sqrt S2 * Real.sqrt s := by
    rw [← Real.sqrt_mul hS20]; exact Real.le_sqrt_of_sq_le hcs
  calc Real.sqrt (∑ c, (max (|(b.1 c : ℝ)| - 1) 0) ^ 2) ≤ Real.sqrt (∑ c, (f c + B) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => pow_le_pow_left₀ (le_max_right _ _) (hle c) 2)
    _ ≤ Real.sqrt S2 + B * Real.sqrt s := by
        rw [Real.sqrt_le_left (by positivity)]
        have hexp : ∑ c, (f c + B) ^ 2 = S2 + 2 * B * ∑ c, f c + s * B ^ 2 := by
          simp only [add_sq, Finset.sum_add_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hS2, Finset.mul_sum]
          congr 2
          exact Finset.sum_congr rfl fun c _ => by ring
        rw [hexp]
        have h1 : Real.sqrt S2 ^ 2 = S2 := Real.sq_sqrt hS20
        have h2 : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt (Nat.cast_nonneg s)
        nlinarith [hcs', Real.sqrt_nonneg S2, Real.sqrt_nonneg (s : ℝ)]

/-- **`thm:corrected`** (lattice form): let `C` be a digital `(0,s)`-sequence over `ℤ/pℤ` whose prefix `P_{sK-1}` satisfies
the corrected skeleton relation (`CorrRel`) and whose partial sums `Ψ_c(j)`, `1 ≤ j ≤ K-1`, are represented by integers
in `[0, B]`. Then any two distinct points of `P_{sK-1}` are at toroidal distance `≥ ℓ_jit^{(B)}(Λ_v) · p^{-K}`. -/
theorem corrected (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (v : Fin s → ZMod p)
    (χ : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) (B : ℕ) (hrel : CorrRel (zcode p) C v χ K)
    (hΨ : ∀ c j, 1 ≤ j → j ≤ K - 1 → ∃ r : ℤ, 0 ≤ r ∧ r ≤ B ∧ (r : ZMod p) = psiSum χ c j) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    ljitB B v ≤ (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
  classical
  set Q : ℕ := p ^ K with hQdef
  have hp := (Fact.out : p.Prime).two_le
  have hQ : 0 < Q := pow_pos (by omega) K
  set n : Fin s → ℕ := fun c => cellIdx (zcode p) C x c K
  set m : Fin s → ℕ := fun c => cellIdx (zcode p) C y c K
  set a : Fin s → ℤ := fun c => cenRep Q ((m c : ℤ) - n c) with ha
  have hn : ∀ c, n c < Q := fun c => cellIdx_lt _ _ _ _ _
  have hm : ∀ c, m c < Q := fun c => cellIdx_lt _ _ _ _ _
  have hD : ∀ c, |((m c : ℤ) - n c)| < Q := fun c => by
    have := hn c; have := hm c; rw [abs_lt]; omega
  have ha0 : a ≠ 0 := by
    intro h0
    apply hxy
    refine skel_inj hs C hseq K hK x y hx hy fun c => ?_
    have := cenRep_eq_zero Q _ (hD c) (congrFun h0 c)
    show n c = m c
    omega
  have hcoord : ∀ c, max (|((a c : ℤ) : ℝ)| - 1) 0 ≤
      (Q : ℝ) * Z3NetDGS.torCoord (seqPoint (zcode p) C x c) (seqPoint (zcode p) C y c) :=
    fun c => torCoord_cell Q hQ _ _ (n c) (m c) (hn c) (hm c) (seqPoint_cell C x c K)
      (seqPoint_cell C y c K) (seqPoint_unit C x c) (seqPoint_unit C y c)
  have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hdist : (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) =
      Real.sqrt (∑ c, ((Q : ℝ) *
        Z3NetDGS.torCoord (seqPoint (zcode p) C x c) (seqPoint (zcode p) C y c)) ^ 2) := by
    unfold Z3NetDGS.torDist2
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq hQr, hQdef]
    push_cast; rfl
  have hJa : Real.sqrt (∑ c, (max (|((a c : ℤ) : ℝ)| - 1) 0) ^ 2) ≤
      (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
    rw [hdist]
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => pow_le_pow_left₀ (le_max_right _ _) (hcoord c) 2)
  refine le_trans ?_ hJa
  by_cases hbig : ∃ c0, (p : ℤ) ≤ |a c0|
  · -- a coarse difference: the lattice vector `p e_{c0}`
    obtain ⟨c0, hc0⟩ := hbig
    set e : Fin s → ℤ := fun c => if c = c0 then (p : ℤ) else 0
    have he0 : e ≠ 0 := fun h => by
      have := congrFun h c0; simp [e] at this; exact (Fact.out : p.Prime).ne_zero this
    have helat : InLat v e := by
      unfold InLat; refine Finset.sum_eq_zero fun c _ => ?_; by_cases h : c = c0 <;> simp [e, h]
    refine (ljitB_le B v e he0 helat).trans ?_
    unfold jitNormB
    rw [Finset.sum_eq_single c0 (fun c _ hc => by simp [e, hc]; linarith [Nat.cast_nonneg (α := ℝ) B]) (by simp)]
    have hpr : (p : ℝ) ≤ |((a c0 : ℤ) : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hc0
    calc Real.sqrt ((max (|((e c0 : ℤ) : ℝ)| - 1 - B) 0) ^ 2) = max (|((e c0 : ℤ) : ℝ)| - 1 - B) 0 :=
          Real.sqrt_sq (le_max_right _ _)
      _ ≤ max (|((a c0 : ℤ) : ℝ)| - 1) 0 := by
          have hec : ((e c0 : ℤ) : ℝ) = p := by simp [e]
          rw [hec, abs_of_nonneg (Nat.cast_nonneg p)]
          have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
          exact max_le_max (by linarith) le_rfl
      _ = Real.sqrt ((max (|((a c0 : ℤ) : ℝ)| - 1) 0) ^ 2) := (Real.sqrt_sq (le_max_right _ _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun c => (max (|((a c : ℤ) : ℝ)| - 1) 0) ^ 2)
          (fun c _ => sq_nonneg _) (mem_univ c0))
  · push Not at hbig
    -- every coordinate: last digit `a_c`, coarse carry `ε_c` of length `j_c`
    have hstep := fun c => coord_step C x y c K hK (hbig c)
    choose hlast ε j hεj hcarry using hstep
    -- the relation for the two points
    have hrx := hrel x hx
    have hry := hrel y hy
    have hdiff : ∑ c, v c * ((a c : ZMod p) + (ε c : ZMod p) * psiSum χ c (j c)) = 0 := by
      have e1 : ∀ c, (seqDigit (zcode p) C y c (K - 1) + ∑ d ∈ Finset.Ico 1 K, χ c d *
          seqDigit (zcode p) C y c (K - 1 - d)) - (seqDigit (zcode p) C x c (K - 1) +
          ∑ d ∈ Finset.Ico 1 K, χ c d * seqDigit (zcode p) C x c (K - 1 - d)) =
          (a c : ZMod p) + (ε c : ZMod p) * psiSum χ c (j c) := by
        intro c
        have hS := corr_sum_diff K (j c) (χ c) (fun d => seqDigit (zcode p) C y c (K - 1 - d))
          (fun d => seqDigit (zcode p) C x c (K - 1 - d)) (ε c : ZMod p) (by
            rcases hεj c with h0 | ⟨-, -, hj1, hj2⟩
            · left; rw [h0]; simp
            · right; exact ⟨hj1, hj2⟩) (fun d hd1 hd2 => hcarry c d hd1 hd2)
        exact comb_sub _ _ _ _ _ _ (hlast c) hS
      rw [← sum_mul_sub_eq_zero (univ : Finset (Fin s)) v _ _ hry hrx]
      exact Finset.sum_congr rfl fun c _ => by rw [e1 c]
    -- the representatives of the partial sums
    have hr : ∀ c, ∃ r : ℤ, 0 ≤ r ∧ r ≤ B ∧
        ((ε c * r : ℤ) : ZMod p) = (ε c : ZMod p) * psiSum χ c (j c) := by
      intro c
      rcases hεj c with h0 | ⟨-, -, hj1, hj2⟩
      · exact ⟨0, le_rfl, Nat.cast_nonneg B, by rw [h0]; simp⟩
      · obtain ⟨r, hr0, hrB, hrΨ⟩ := hΨ c (j c) hj1 hj2
        exact ⟨r, hr0, hrB, by rw [Int.cast_mul, hrΨ]⟩
    choose r hr0 hrB hrcast using hr
    set b : Fin s → ℤ := fun c => a c + ε c * r c with hb
    have hblat : InLat v b := by
      unfold InLat
      rw [← hdiff]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hb]; push_cast
      rw [show ((ε c : ZMod p) * (r c : ZMod p)) = (((ε c * r c : ℤ)) : ZMod p) by push_cast; rfl, hrcast c]
    -- `|b_c| = |a_c| + |ε_c r_c|`
    have hbabs : ∀ c, |a c| ≤ |b c| ∧ |b c| ≤ |a c| + B := by
      intro c
      have hbc : b c = a c + ε c * r c := rfl
      have hB0 : (0 : ℤ) ≤ B := Nat.cast_nonneg B
      rw [hbc]
      rcases hεj c with h0 | ⟨hε, hεa, -, -⟩
      · rw [h0, zero_mul, add_zero]; exact ⟨le_rfl, by linarith⟩
      · rcases hε with h1 | h1
        · rw [h1, one_mul] at hεa ⊢
          rw [abs_of_pos hεa, abs_of_pos (by linarith [hr0 c])]
          constructor <;> linarith [hr0 c, hrB c]
        · rw [h1] at hεa ⊢
          have : a c < 0 := by linarith
          rw [abs_of_neg this, abs_of_neg (by linarith [hr0 c])]
          constructor <;> linarith [hr0 c, hrB c]
    have hb0 : b ≠ 0 := by
      intro h0
      apply ha0
      funext c
      have := (hbabs c).1
      rw [congrFun h0 c, Pi.zero_apply, abs_zero] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    refine (ljitB_le B v b hb0 hblat).trans ?_
    unfold jitNormB
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => pow_le_pow_left₀ (le_max_right _ _) ?_ 2)
    have h1 : |((b c : ℤ) : ℝ)| ≤ |((a c : ℤ) : ℝ)| + B := by
      rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast (hbabs c).2
    exact max_le_max (by linarith) le_rfl

/-- **`thm:corrected`**: `sep(P_{sK-1}) ≥ p^{-1/s} ℓ_jit^{(B)}(Λ_v)`. -/
theorem corrected_sepAtPrefix (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (v : Fin s → ZMod p) (χ : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) (B : ℕ)
    (hrel : CorrRel (zcode p) C v χ K)
    (hΨ : ∀ c j, 1 ≤ j → j ≤ K - 1 → ∃ r : ℤ, 0 ≤ r ∧ r ≤ B ∧ (r : ZMod p) = psiSum χ c j) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) C) ((p : ℝ) ^ (-(1 / (s : ℝ))) * ljitB B v) := by
  intro x y hx hy hxy
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := corrected hs C hseq v χ K hK B hrel hΨ x y hx hy hxy
  have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  calc (p : ℝ) ^ (-(1 / (s : ℝ))) * ljitB B v * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))
      = ljitB B v * ((p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))) := by ring
    _ = ljitB B v / (p : ℝ) ^ K := by rw [prefix_scale hp (by omega) K hK, div_eq_mul_inv]
    _ ≤ _ := by rw [div_le_iff₀ hpK]; linarith

end GeoSeq
