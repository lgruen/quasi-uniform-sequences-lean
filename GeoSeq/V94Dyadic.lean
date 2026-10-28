/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V94Thm

@[expose] public section

/-!
# GeoSeq stage V9-4 (part 3): dyadic weights (`cor:dyadic`)

* `signed_pow_two_ne_zero`, `abs_signed_pow_two_lt`: `A = ∑_c e_c 2^{o(c)}` with `e ∈ {-1,0,1}`, `e ≠ 0` and `o`
  injective with values `< s - 1` on the support satisfies `0 < |A| ≤ 2^{s-1} - 1`.
* `cabsZ_ge_of_mul`: if `2^{s-1} x = A` in `ℤ/pℤ` with `0 < |A| < 2^{s-1}`, then `|x|_∘ ≥ ⌊p/2^{s-1}⌋`.
* `cabsZ_dyadic`: the dyadic lower bound `|k · e'|_∘ ≥ ⌊p/2^{s-1}⌋` for every step `e'`.
* `exists_small_step` (pigeonhole on the cycle `ℤ/pℤ`): for every weights `k` some step has
  `|k · e'|_∘ ≤ ⌊p/2^{s-1}⌋` (the `2^{s-1}` subset sums with arcs of length `⌊p/2^{s-1}⌋ + 1` would not fit).
* **`betaStar_dyadic`**, **`betaStar_le_dyadic`**, **`betaStar_pos_imp`**, **`dyadic_qu`** (`cor:dyadic`):
  `β(dyadic) = (⌊p/2^{s-1}⌋ - 1)/p`; no weights give more; `β(k) > 0` only if `p > 2^s`; for every prime
  `p > 2^s` the staggered residue sequence with dyadic weights is a quasi-uniform digital `(0,s)`-sequence with
  `sep(P_{sK}) ≥ (⌊p/2^{s-1}⌋ - 1)/p` for every `K ≥ 1`. `stdOrder_*`: the standard order is admissible.
-/

namespace GeoSeq

open Finset

variable {s : ℕ}

/-- A signed sum of distinct powers of two is nonzero: if `e ∈ {-1,0,1}^s` is not `0` and `o` is injective on
its support, then `∑_c e_c 2^{o(c)} ≠ 0` (the term of the smallest exponent is not divisible by the next power). -/
theorem signed_pow_two_ne_zero (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0)
    (o : Fin s → ℕ) (ho : ∀ c c', e c ≠ 0 → e c' ≠ 0 → o c = o c' → c = c') :
    ∑ c, e c * 2 ^ o c ≠ 0 := by
  classical
  set T := univ.filter fun c => e c ≠ 0 with hT
  have hTne : T.Nonempty := by obtain ⟨c, hc⟩ := hne; exact ⟨c, by simp [hT, hc]⟩
  obtain ⟨c0, hc0T, hmin⟩ := T.exists_min_image o hTne
  have hc0 : e c0 ≠ 0 := by simpa [hT] using hc0T
  have hsum : ∑ c, e c * 2 ^ o c = ∑ c ∈ T, e c * 2 ^ o c := by
    rw [hT, Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by split_ifs with h <;> simp_all
  rw [hsum, ← Finset.add_sum_erase _ _ hc0T]
  intro h0
  have hdvd : (2 : ℤ) ^ (o c0 + 1) ∣ ∑ c ∈ T.erase c0, e c * 2 ^ o c := by
    refine Finset.dvd_sum fun c hc => ?_
    have hcT := Finset.mem_of_mem_erase hc
    have hcc0 := Finset.ne_of_mem_erase hc
    have hle := hmin c hcT
    have hne' : o c ≠ o c0 := fun h => hcc0 (ho c c0 (by simpa [hT] using hcT) hc0 h)
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  have h1 : (2 : ℤ) ^ (o c0 + 1) ∣ e c0 * 2 ^ o c0 := by
    have : e c0 * 2 ^ o c0 = -∑ c ∈ T.erase c0, e c * 2 ^ o c := by linarith
    rw [this]; exact (dvd_neg).mpr hdvd
  have hu : e c0 = 1 ∨ e c0 = -1 := by have := he c0; omega
  have h2 : (2 : ℤ) ^ (o c0 + 1) ∣ 2 ^ o c0 := by
    rcases hu with hu | hu <;> rw [hu] at h1
    · simpa using h1
    · simpa using h1
  have := Int.le_of_dvd (by positivity) h2
  rw [pow_succ] at this
  have : (0 : ℤ) < 2 ^ o c0 := by positivity
  linarith

lemma geom_two (n : ℕ) : ∑ j ∈ range n, (2 : ℤ) ^ j + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith

/-- `|∑_c e_c 2^{o(c)}| ≤ 2^{s-1} - 1` when `o` is injective with values `< s - 1` on the support of `e`. -/
theorem abs_signed_pow_two_lt (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (o : Fin s → ℕ)
    (ho : ∀ c c', e c ≠ 0 → e c' ≠ 0 → o c = o c' → c = c') (hlt : ∀ c, e c ≠ 0 → o c < s - 1) :
    |∑ c, e c * 2 ^ o c| < 2 ^ (s - 1) := by
  classical
  set T := univ.filter fun c => e c ≠ 0 with hT
  have h1 : |∑ c, e c * 2 ^ o c| ≤ ∑ c ∈ T, (2 : ℤ) ^ o c := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hT, Finset.sum_filter]
    refine Finset.sum_le_sum fun c _ => ?_
    split_ifs with h
    · rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ o c)]
      have : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
      nlinarith [(by positivity : (0 : ℤ) < 2 ^ o c)]
    · push Not at h; simp [h]
  have hinj : Set.InjOn o T := fun c hc c' hc' h =>
    ho c c' (by simpa [hT] using hc) (by simpa [hT] using hc') h
  have h2 : ∑ c ∈ T, (2 : ℤ) ^ o c = ∑ j ∈ T.image o, (2 : ℤ) ^ j :=
    (Finset.sum_image (f := fun j => (2 : ℤ) ^ j) hinj).symm
  have h3 : ∑ j ∈ T.image o, (2 : ℤ) ^ j ≤ ∑ j ∈ range (s - 1), (2 : ℤ) ^ j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro j hj
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hlt c (by simpa [hT] using hc))
  have h4 := geom_two (s - 1)
  linarith

lemma cabsZ_le_val {p : ℕ} (x : ZMod p) : cabsZ x ≤ x.val := min_le_left _ _

lemma cabsZ_neg {p : ℕ} [NeZero p] (x : ZMod p) : cabsZ (-x) = cabsZ x := by
  unfold cabsZ
  rw [ZMod.neg_val]
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]; have := ZMod.val_lt x; omega

/-- The centred representative: an integer `X ≡ x (mod p)` with `|X| = |x|_∘`. -/
lemma exists_centred {p : ℕ} [NeZero p] (x : ZMod p) : ∃ X : ℤ, (X : ZMod p) = x ∧ X.natAbs = cabsZ x := by
  have hv := ZMod.val_lt x
  by_cases h : x.val ≤ p - x.val
  · refine ⟨x.val, by simp, ?_⟩
    unfold cabsZ; rw [min_eq_left h, Int.natAbs_natCast]
  · refine ⟨(x.val : ℤ) - p, by simp, ?_⟩
    unfold cabsZ; rw [min_eq_right (by omega)]; omega

/-- **The dyadic estimate** (proof of `cor:dyadic`, first part): if `2^{s-1} x = A` in `ℤ/pℤ` for an integer `A`
with `0 < |A| < 2^{s-1}`, then `|x|_∘ ≥ ⌊p/2^{s-1}⌋`. -/
theorem cabsZ_ge_of_mul {p : ℕ} [NeZero p] (M : ℕ) (x : ZMod p) (A : ℤ) (hA0 : A ≠ 0)
    (hAM : |A| < M) (hx : (M : ZMod p) * x = A) : p / M ≤ cabsZ x := by
  obtain ⟨X, hX, hXc⟩ := exists_centred x
  have hdvd : (p : ℤ) ∣ M * X - A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hX, hx]; ring
  have hne : (M : ℤ) * X - A ≠ 0 := by
    intro h
    have hMA : (M : ℤ) ∣ A := ⟨X, by linarith⟩
    have := Int.le_of_dvd (abs_pos.mpr hA0) ((dvd_abs _ _).mpr hMA)
    linarith
  have hp : (p : ℤ) ≤ |(M : ℤ) * X - A| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have habs : |(M : ℤ) * X - A| ≤ M * |X| + |A| := by
    calc |(M : ℤ) * X - A| ≤ |(M : ℤ) * X| + |A| := abs_sub _ _
      _ = M * |X| + |A| := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ M)]
  have hXa : |X| = (cabsZ x : ℤ) := by rw [Int.abs_eq_natAbs, hXc]
  rw [hXa] at habs
  have hlt : (p : ℤ) < M * ((cabsZ x : ℤ) + 1) := by linarith
  have hlt' : p < (cabsZ x + 1) * M := by
    have : (p : ℤ) < ((cabsZ x + 1) * M : ℕ) := by push_cast; linarith
    exact_mod_cast this
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hAM; simp at hAM; exact absurd (abs_nonneg A) (not_le.mpr hAM)
    · exact h
  have := (Nat.div_lt_iff_lt_mul hM).mpr hlt'
  omega

section NZ
variable {p : ℕ} [NeZero p]

lemma cabsZ_cast_sub (i j : ℕ) (hi : i < p) (hj : j < p) :
    cabsZ ((j : ZMod p) - (i : ZMod p)) ≤ max (j - i) (i - j) := by
  rcases le_total i j with h | h
  · have : (j : ZMod p) - i = ((j - i : ℕ) : ZMod p) := by rw [Nat.cast_sub h]
    rw [this]
    refine (cabsZ_le_val _).trans ?_
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; exact le_max_left _ _
  · have : (j : ZMod p) - i = -((i - j : ℕ) : ZMod p) := by rw [Nat.cast_sub h]; ring
    rw [this, cabsZ_neg ((i - j : ℕ) : ZMod p)]
    refine (cabsZ_le_val _).trans ?_
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; exact le_max_right _ _

/-- **Pigeonhole on the cycle** (`cor:dyadic`, second part): for every weights `k ∈ (ℤ/pℤ)^s` some step `e'`
(`e'_{c⋆} = 0`, `e' ∈ {-1,0,1}^s \ {0}`) has `|k · e'|_∘ ≤ ⌊p/2^{s-1}⌋`: otherwise the `2^{s-1}` subset sums
`S_A = ∑_{c ∈ A} k_c` (`A ⊆ C`) would carry pairwise disjoint arcs of `⌊p/2^{s-1}⌋ + 1` points. -/
theorem exists_small_step (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) :
    ∃ e, StarStep cs e ∧ cabsZ (∑ c, (e c : ZMod p) * k c) ≤ p / 2 ^ (s - 1) := by
  classical
  by_contra hcon
  push Not at hcon
  set M := 2 ^ (s - 1) with hM
  set d := p / M + 1 with hd
  have hM2 : 2 ≤ M := by
    rw [hM]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hdp : d ≤ p := by
    have : p / M < p := Nat.div_lt_self (by omega) (by omega)
    omega
  set Ss := (univ.erase cs).powerset with hSs
  let S : Finset (Fin s) → ZMod p := fun A => ∑ c ∈ A, k c
  let arc : Finset (Fin s) → Finset (ZMod p) := fun A => (range d).image fun i : ℕ => S A + (i : ZMod p)
  have hcard : ∀ A, (arc A).card = d := by
    intro A
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < p := lt_of_lt_of_le (Finset.mem_range.mp hi) hdp
    have hj' : j < p := lt_of_lt_of_le (Finset.mem_range.mp hj) hdp
    have : (i : ZMod p) = j := add_left_cancel hij
    have := congrArg ZMod.val this
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at this
  have hdisj : (Ss : Set (Finset (Fin s))).PairwiseDisjoint arc := by
    intro A hA B hB hAB
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hxB
    have hA' : A ⊆ univ.erase cs := Finset.mem_powerset.mp hA
    have hB' : B ⊆ univ.erase cs := Finset.mem_powerset.mp hB
    set e : Fin s → ℤ := fun c => (if c ∈ A then 1 else 0) - (if c ∈ B then 1 else 0) with he
    have hst : StarStep cs e := by
      refine ⟨fun c => by simp only [he]; split_ifs <;> norm_num, ?_, ?_⟩
      · have h1 : cs ∉ A := fun h => by simpa using hA' h
        have h2 : cs ∉ B := fun h => by simpa using hB' h
        simp [he, h1, h2]
      · by_contra hz
        push Not at hz
        apply hAB
        ext c
        have := hz c
        simp only [he] at this
        constructor <;> intro h <;> by_contra h' <;> simp [h, h'] at this
    have hσ : ∑ c, (e c : ZMod p) * k c = S A - S B := by
      simp only [he, S]
      push_cast
      simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_mem,
        Finset.univ_inter]
    have h1 := hcon e hst
    rw [hσ] at h1
    have h2 : S A - S B = (j : ZMod p) - i := by linear_combination -hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have h3 : cabsZ (S A - S B) ≤ max (j - i) (i - j) := by
      rw [h2]; exact cabsZ_cast_sub i j (by omega) (by omega)
    omega
  have hU := Finset.card_biUnion hdisj
  have hle : (Ss.biUnion arc).card ≤ p := by
    calc (Ss.biUnion arc).card ≤ (univ : Finset (ZMod p)).card := Finset.card_le_univ _
      _ = p := ZMod.card p
  rw [Finset.sum_congr rfl fun A _ => hcard A, Finset.sum_const, smul_eq_mul, hSs,
    Finset.card_powerset, Finset.card_erase_of_mem (mem_univ cs), card_univ, Fintype.card_fin] at hU
  rw [hU] at hle
  have : p < M * d := by
    rw [hd, mul_add, mul_one]
    have := Nat.lt_div_mul_add (a := p) (b := M) (by omega)
    rw [mul_comm]; omega
  rw [← hM] at hle
  omega

end NZ

variable {p : ℕ} [Fact p.Prime]

lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

/-- **`cor:dyadic`**, lower bound: for an odd prime `p`, every step `e'` has `|k · e'|_∘ ≥ ⌊p/2^{s-1}⌋` for the
dyadic weights `k_c = 2^{o(c)}/2^{s-1}` (`o` injective on `C` with values `< s - 1`). -/
theorem cabsZ_dyadic (hp2 : p ≠ 2) (cs : Fin s) (o : Fin s → ℕ)
    (ho : ∀ c c', c ≠ cs → c' ≠ cs → o c = o c' → c = c') (hlt : ∀ c, c ≠ cs → o c < s - 1)
    (e : Fin s → ℤ) (he : StarStep cs e) :
    p / 2 ^ (s - 1) ≤ cabsZ (∑ c, (e c : ZMod p) * dyadicK p o c) := by
  obtain ⟨hb, hcs, hne⟩ := he
  have hsupp : ∀ c, e c ≠ 0 → c ≠ cs := fun c h hc => h (hc ▸ hcs)
  have hinj : ∀ c c', e c ≠ 0 → e c' ≠ 0 → o c = o c' → c = c' := fun c c' h h' =>
    ho c c' (hsupp c h) (hsupp c' h')
  have hA := abs_signed_pow_two_lt e hb o hinj fun c h => hlt c (hsupp c h)
  have hA' : |∑ c, e c * 2 ^ o c| < ((2 ^ (s - 1) : ℕ) : ℤ) := by push_cast; exact hA
  refine cabsZ_ge_of_mul (2 ^ (s - 1)) _ (∑ c, e c * 2 ^ o c)
    (signed_pow_two_ne_zero e hb hne o hinj) hA' ?_
  have h2 := two_ne_zero_of_ne_two hp2
  simp only [dyadicK, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  have : (2 : ZMod p) ^ (s - 1) * ((2 : ZMod p)⁻¹) ^ (s - 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ h2, one_pow]
  linear_combination ((e c : ZMod p) * 2 ^ o c) * this

lemma dyadicK_ne (hp2 : p ≠ 2) (o : Fin s → ℕ) (c : Fin s) : dyadicK p o c ≠ 0 := by
  have h2 := two_ne_zero_of_ne_two hp2
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ (inv_ne_zero h2))

/-- **`cor:dyadic`** (optimality): for every weights `k`, `β(k) ≤ (⌊p/2^{s-1}⌋ - 1)/p`. -/
theorem betaStar_le_dyadic (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) :
    betaStar p cs k ≤ (((p / 2 ^ (s - 1) : ℕ) : ℝ) - 1) / p := by
  obtain ⟨e, he, hle⟩ := exists_small_step hs cs k
  refine (betaStar_le p cs k e he).trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg p))
  have : (cabsZ (∑ c, (e c : ZMod p) * k c) : ℝ) ≤ ((p / 2 ^ (s - 1) : ℕ) : ℝ) := by exact_mod_cast hle
  linarith

/-- **`cor:dyadic`** (value): for an odd prime `p` and an admissible order `o`,
`β(dyadic) = (⌊p/2^{s-1}⌋ - 1)/p`. -/
theorem betaStar_dyadic (hp2 : p ≠ 2) (hs : 2 ≤ s) (cs : Fin s) (o : Fin s → ℕ)
    (ho : ∀ c c', c ≠ cs → c' ≠ cs → o c = o c' → c = c') (hlt : ∀ c, c ≠ cs → o c < s - 1) :
    betaStar p cs (dyadicK p o) = (((p / 2 ^ (s - 1) : ℕ) : ℝ) - 1) / p := by
  refine le_antisymm (betaStar_le_dyadic hs cs _) (le_betaStar p hs cs _ _ fun e he => ?_)
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg p)
  have := cabsZ_dyadic hp2 cs o ho hlt e he
  have : ((p / 2 ^ (s - 1) : ℕ) : ℝ) ≤ (cabsZ (∑ c, (e c : ZMod p) * dyadicK p o c) : ℝ) := by
    exact_mod_cast this
  linarith

/-- **`cor:dyadic`** ("only if"): if `β(k) > 0` for some weights `k`, then `p > 2^s`. -/
theorem betaStar_pos_imp (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) (hβ : 0 < betaStar p cs k) :
    2 ^ s < p := by
  have h := hβ.trans_le (betaStar_le_dyadic hs cs k)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : (1 : ℝ) < ((p / 2 ^ (s - 1) : ℕ) : ℝ) := by
    have := (div_pos_iff_of_pos_right hp0).mp h; linarith
  have h2 : 2 ≤ p / 2 ^ (s - 1) := by exact_mod_cast h1
  have h3 : 2 * 2 ^ (s - 1) ≤ p := by
    have := (Nat.le_div_iff_mul_le (by positivity)).mp h2; linarith
  have h4 : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [← h4] at h3
  rcases h3.lt_or_eq with h5 | h5
  · exact h5
  · exfalso
    have h2 : 2 ∣ p := h5 ▸ dvd_pow_self 2 (by omega)
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 2 h2 with h | h
    · omega
    · have : 4 ≤ 2 ^ s := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      omega

/-- The standard order is admissible: injective on `C` with values `< s - 1`. -/
lemma stdOrder_inj (cs : Fin s) (c c' : Fin s) (hc : c ≠ cs) (hc' : c' ≠ cs)
    (h : stdOrder cs c = stdOrder cs c') : c = c' := by
  have h1 : (c : ℕ) ≠ cs := fun e => hc (Fin.ext e)
  have h2 : (c' : ℕ) ≠ cs := fun e => hc' (Fin.ext e)
  unfold stdOrder at h
  apply Fin.ext
  split_ifs at h <;> omega

lemma stdOrder_lt (cs : Fin s) (c : Fin s) (hc : c ≠ cs) : stdOrder cs c < s - 1 := by
  have h1 : (c : ℕ) ≠ cs := fun e => hc (Fin.ext e)
  have := c.isLt; have := cs.isLt
  unfold stdOrder; split_ifs <;> omega

/-- **`cor:dyadic`** ("in particular"): for every `s ≥ 2` and every prime `p > 2^s`, the staggered residue sequence
with dyadic weights (any admissible order, distinct places, `θ, μ⋆ ≠ 0`) is a digital `(0,s)`-sequence with
`sep(P_{sK}) ≥ (⌊p/2^{s-1}⌋ - 1)/p` for every `K ≥ 1`, and it is quasi-uniform. -/
theorem dyadic_qu (hs : 2 ≤ s) (hps : 2 ^ s < p) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (o : Fin s → ℕ)
    (ho : ∀ c c', c ≠ cs → c' ≠ cs → o c = o c' → c = c') (hlt : ∀ c, c ≠ cs → o c < s - 1) :
    IsSeq0 (zcode p) (resStar a θ cs μs (dyadicK p o)) ∧
      (∀ K, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (resStar a θ cs μs (dyadicK p o)))
        ((((p / 2 ^ (s - 1) : ℕ) : ℝ) - 1) / p)) ∧
      IsQuasiUniform (seqPoint (zcode p) (resStar a θ cs μs (dyadicK p o))) := by
  have h4 : 4 ≤ 2 ^ s := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hk : ∀ c, c ≠ cs → dyadicK p o c ≠ 0 := fun c _ => dyadicK_ne hp2 o c
  have hβ := betaStar_dyadic hp2 hs cs o ho hlt
  have hpos : 0 < betaStar p cs (dyadicK p o) := by
    rw [hβ]
    have h2 : 2 ≤ p / 2 ^ (s - 1) := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      have : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have : (2 : ℝ) ≤ ((p / 2 ^ (s - 1) : ℕ) : ℝ) := by exact_mod_cast h2
    exact div_pos (by linarith) (by exact_mod_cast (show 0 < p by omega))
  refine ⟨resStar_t0 (zcode p) a ha θ hθ cs μs hμ _ hk, fun K hK => ?_,
    residuestar_qu hp5 hs a ha θ hθ cs μs hμ _ hk hpos⟩
  rw [← hβ]
  exact residuestar_sep hp5 hs a ha θ hθ cs μs hμ _ hk K hK

end GeoSeq
