/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V95Gen

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 4): `rem:randomize`(b), (c) — index scrambles and reorderings

Stage V9-5 proved: reorderings that permute every prefix `{0, …, p^m - 1}` keep the close pairs and the failure of
quasi-uniformity (`close_comp`, `not_qu_comp`), and the Gray code is such a reordering.

* **(c) reorderings that keep only the prefixes of a level family**: `close_lev` (close pairs at arbitrary levels give
  close pairs at the levels of any family with bounded gaps, at the cost of a factor `p^Δ`), **`not_qu_comp_lev`**
  (a reordering that permutes the prefixes `{0, …, p^m - 1}` only for `m` in a family with bounded gaps keeps the
  failure of quasi-uniformity), **`not_qu_comp_full`** (the paper's case: the full levels `m ∈ sℕ`).
* **(b) index scrambles** `C_c ↦ C_c U` (one `U` for all coordinates, upper triangular — only the entries `U[k][j]`,
  `k ≤ j`, enter — with nonzero diagonal): `genY_idxScr` (digits of `C U` at `V` = digits of `C` at `U V`),
  `uMul_surj` (back substitution), **`idxScr_prefix`** (every prefix `P_m` is the same set for `C` and `C U`),
  **`idxScr_not_qu`** (close pairs of `C` make `C U` not quasi-uniform).
-/

namespace GeoSeq

open Finset Polynomial

section Lev
variable {s : ℕ}

lemma rpow_shift_le (p : ℕ) (hp : 1 ≤ p) (m m' Δ : ℕ) (h1 : m ≤ m') (h2 : m' ≤ m + Δ) :
    ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) ≤ (p : ℝ) ^ Δ * ((p : ℝ) ^ m') ^ (-(1 : ℝ) / s) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hm' : (p : ℝ) ^ m' = (p : ℝ) ^ m * (p : ℝ) ^ (m' - m) := by rw [← pow_add]; congr 1; omega
  rw [hm', Real.mul_rpow (by positivity) (by positivity)]
  have hx : 0 < ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := Real.rpow_pos_of_pos (by positivity) _
  have hd1 : (1 : ℝ) ≤ (p : ℝ) ^ (m' - m) := one_le_pow₀ hp1
  have hy : ((p : ℝ) ^ (m' - m))⁻¹ ≤ ((p : ℝ) ^ (m' - m)) ^ (-(1 : ℝ) / s) := by
    rw [← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hd1 ?_
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ s := by exact_mod_cast h
      rw [neg_div, neg_le_neg_iff, div_le_one (by positivity)]; exact this
  have hΔ : (p : ℝ) ^ (m' - m) ≤ (p : ℝ) ^ Δ := pow_le_pow_right₀ hp1 (by omega)
  have h3 : 1 ≤ (p : ℝ) ^ Δ * ((p : ℝ) ^ (m' - m)) ^ (-(1 : ℝ) / s) := by
    calc (1 : ℝ) = (p : ℝ) ^ (m' - m) * ((p : ℝ) ^ (m' - m))⁻¹ := by field_simp
      _ ≤ (p : ℝ) ^ Δ * ((p : ℝ) ^ (m' - m)) ^ (-(1 : ℝ) / s) :=
          mul_le_mul hΔ hy (inv_nonneg.mpr (by positivity)) (by positivity)
  nlinarith

/-- Close pairs at arbitrary levels give close pairs at the levels of a family with gaps `≤ Δ`
(`rem:randomize`(c)). -/
theorem close_lev {p : ℕ} (hp : 1 ≤ p) (pt : ℕ → Fin s → ℝ) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, Lev m ∧ v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
  intro ε hε
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨m, v, w, hv, hw, hvw, hd⟩ := hclose (ε / (p : ℝ) ^ Δ) (by positivity)
  obtain ⟨m', hL, hm1, hm2⟩ := hgap m
  have hpm : p ^ m ≤ p ^ m' := Nat.pow_le_pow_right hp hm1.le
  refine ⟨m', v, w, hL, hv.trans_le hpm, hw.trans_le hpm, hvw, hd.trans_le ?_⟩
  have := rpow_shift_le (s := s) p hp m m' Δ hm1.le hm2
  calc ε / (p : ℝ) ^ Δ * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)
      ≤ ε / (p : ℝ) ^ Δ * ((p : ℝ) ^ Δ * ((p : ℝ) ^ m') ^ (-(1 : ℝ) / s)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = ε * ((p : ℝ) ^ m') ^ (-(1 : ℝ) / s) := by field_simp

/-- **`rem:randomize`(c), general level family**: if a sequence has close pairs (as in `thm:nonqu`), then every
reordering `σ` that permutes the prefix `{0, …, p^m - 1}` for every `m` of a level family with bounded gaps gives a
sequence that is not quasi-uniform. -/
theorem not_qu_comp_lev {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ) (σ : ℕ → ℕ)
    (hσ : ∀ m, Lev m → ∀ v, v < p ^ m → ∃ v', v' < p ^ m ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (pt ∘ σ) := by
  refine not_qu_of_close hp hs _ (fun v c => hpt (σ v) c) fun ε hε => ?_
  obtain ⟨m, v, w, hL, hv, hw, hvw, hd⟩ := close_lev (by omega) pt Lev Δ hgap hclose ε hε
  obtain ⟨v', hv', rfl⟩ := hσ m hL v hv
  obtain ⟨w', hw', rfl⟩ := hσ m hL w hw
  exact ⟨m, v', w', hv', hw', fun h => hvw (by rw [h]), hd⟩

lemma hasGap_full (hs : 1 ≤ s) : HasGap (levFull s) s := by
  intro m
  refine ⟨s * (m / s + 1), ⟨m / s + 1, Nat.le_add_left 1 _, rfl⟩, ?_, ?_⟩
  · have := Nat.lt_mul_div_succ m (show 0 < s by omega); linarith
  · have := Nat.mul_div_le m s; rw [Nat.mul_succ]; linarith

/-- **`rem:randomize`(c)** (as stated): reorderings that keep every full level `P_{sK}` as a set do not restore
quasi-uniformity of a sequence with close pairs (every sequence covered by `thm:nonqu`, `nonqu`). -/
theorem not_qu_comp_full {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (σ : ℕ → ℕ)
    (hσ : ∀ K, 1 ≤ K → ∀ v, v < p ^ (s * K) → ∃ v', v' < p ^ (s * K) ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (pt ∘ σ) :=
  not_qu_comp_lev hp hs pt hpt (levFull s) s (hasGap_full hs) σ
    (fun m ⟨K, hK, hm⟩ v hv => by subst hm; exact hσ K hK v hv) hclose

end Lev

section UMul
variable {F : Type*} [Field F]

lemma colPoly_coeff (U : ℕ → ℕ → F) (j k : ℕ) : (colPoly U j).coeff k = if k ≤ j then U k j else 0 := by
  unfold colPoly
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

lemma uMul_add (U : ℕ → ℕ → F) (V W : F[X]) : uMul U (V + W) = uMul U V + uMul U W :=
  Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])

lemma uMul_monomial (U : ℕ → ℕ → F) (m : ℕ) (t : F) : uMul U (monomial m t) = C t * colPoly U m :=
  Polynomial.sum_monomial_index _ _ (by simp)

lemma uMul_zero (U : ℕ → ℕ → F) : uMul U 0 = 0 := Polynomial.sum_zero_index _

lemma uMul_coeff (U : ℕ → ℕ → F) (V : F[X]) (k : ℕ) :
    (uMul U V).coeff k = ∑ j ∈ range (V.natDegree + 1), V.coeff j * (if k ≤ j then U k j else 0) := by
  unfold uMul
  rw [Polynomial.sum_over_range' _ (fun _ => by simp) _ (Nat.lt_succ_self _), finsetSum_coeff]
  simp_rw [coeff_C_mul, colPoly_coeff]

lemma uMul_degree (U : ℕ → ℕ → F) (V : F[X]) (m : ℕ) (hV : V.degree < m) : (uMul U V).degree < m := by
  rw [degree_lt_iff_coeff_zero] at hV ⊢
  intro k hk
  rw [uMul_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : m ≤ j
  · rw [hV j hj, zero_mul]
  · rw [if_neg (by omega), mul_zero]

/-- **Back substitution**: an upper-triangular `U` with nonzero diagonal maps the polynomials of degree `< m` onto
themselves. -/
theorem uMul_surj (U : ℕ → ℕ → F) (hU : ∀ k, U k k ≠ 0) :
    ∀ m : ℕ, ∀ W : F[X], W.degree < (m : WithBot ℕ) → ∃ V : F[X], V.degree < (m : WithBot ℕ) ∧ uMul U V = W := by
  intro m
  induction m with
  | zero =>
    intro W hW
    have : W = 0 := by
      ext k; rw [degree_lt_iff_coeff_zero] at hW; simpa using hW k (Nat.zero_le _)
    exact ⟨0, by simp, by rw [uMul_zero, this]⟩
  | succ m ih =>
    intro W hW
    set t := W.coeff m / U m m with ht
    obtain ⟨V', hV', hUV'⟩ := ih (W - C t * colPoly U m) (by
      rw [degree_lt_iff_coeff_zero] at hW ⊢
      intro k hk
      rw [coeff_sub, coeff_C_mul, colPoly_coeff]
      rcases eq_or_lt_of_le hk with h | hk'
      · rw [← h, if_pos le_rfl, ht, div_mul_cancel₀ _ (hU m), sub_self]
      · rw [hW k (by omega), if_neg (by omega), mul_zero, sub_zero])
    refine ⟨V' + monomial m t, ?_, ?_⟩
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (hV'.trans_le ?_) ?_)
      · exact_mod_cast Nat.le_succ m
      · exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast Nat.lt_succ_self m)
    · rw [uMul_add, uMul_monomial, hUV']; ring

variable {s : ℕ}

lemma genY_range (C : Gen s F) (c : Fin s) (W : F[X]) (n M : ℕ) (hM : 1 ≤ M) (hW : W.degree < M) :
    genY C c W n = ∑ k ∈ range M, C c n k * W.coeff k := by
  unfold genY
  refine Polynomial.sum_over_range' _ (fun _ => by simp) _ ?_
  by_cases h0 : W = 0
  · subst h0; simp; omega
  · exact (natDegree_lt_iff_degree_lt h0).mpr hW

/-- The digits of the index scramble `C U` at `V` are the digits of `C` at `U V`. -/
theorem genY_idxScr (C : Gen s F) (U : ℕ → ℕ → F) (c : Fin s) (V : F[X]) (n : ℕ) :
    genY (idxScr C U) c V n = genY C c (uMul U V) n := by
  set M := V.natDegree + 1
  have hVM : V.degree < M := by
    by_cases h0 : V = 0
    · subst h0; simp [M]
    · exact (natDegree_lt_iff_degree_lt h0).mp (Nat.lt_succ_self _)
  rw [genY_range _ c V n M (by omega) hVM, genY_range _ c _ n M (by omega) (uMul_degree U V M hVM)]
  simp_rw [uMul_coeff, idxScr]
  have hinner : ∀ j ∈ range M, (∑ k ∈ range (j + 1), C c n k * U k j) * V.coeff j =
      ∑ k ∈ range M, C c n k * (V.coeff j * (if k ≤ j then U k j else 0)) := by
    intro j hj
    have hjM := Finset.mem_range.mp hj
    rw [Finset.sum_mul]
    have : range (j + 1) = (range M).filter (fun k => k ≤ j) := by
      ext k; simp only [Finset.mem_range, Finset.mem_filter]; omega
    rw [this, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]

end UMul

section IdxPrime
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

omit [Fact p.Prime] in
lemma sum_digits_mod (v : ℕ) : ∀ n, ∑ k ∈ range n, (v / p ^ k % p) * p ^ k = v % p ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by rw [Finset.sum_range_succ, sum_digits_mod v n, Nat.mod_pow_succ]; ring

/-- `ι(idxPoly(v)) = v`. -/
theorem polyIdx_idxPolyP (v : ℕ) : polyIdx p (idxPolyP p v) = v := by
  have hp := (Fact.out : p.Prime)
  have hdeg := natDegree_idxPolyP (p := p) v
  unfold polyIdx
  rw [Finset.sum_subset (Finset.range_subset_range.mpr (show (idxPolyP p v).natDegree + 1 ≤ v + 1 by omega))
    (fun k _ hk => by
      rw [coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range] at hk; omega), ZMod.val_zero, zero_mul])]
  have e : ∀ k ∈ range (v + 1), ((idxPolyP p v).coeff k).val * p ^ k = (v / p ^ k % p) * p ^ k := by
    intro k hk
    rw [coeff_idxPolyP, if_pos (Finset.mem_range.mp hk), ZMod.val_natCast, Nat.mod_mod]
  rw [Finset.sum_congr rfl e, sum_digits_mod, Nat.mod_eq_of_lt]
  exact (Nat.lt_pow_self hp.one_lt).trans (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self v))

lemma idxPolyP_degree_lt (v m : ℕ) (hv : v < p ^ m) : (idxPolyP p v).degree < m := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_idxPolyP]
  split_ifs
  · rw [Nat.div_eq_of_lt (hv.trans_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk)), Nat.zero_mod,
      Nat.cast_zero]
  · rfl

lemma polyIdx_lt_of_degree (W : (ZMod p)[X]) (m : ℕ) (hW : W.degree < m) : polyIdx p W < p ^ m := by
  by_cases h0 : W = 0
  · subst h0; simp [polyIdx]; exact pow_pos (Fact.out : p.Prime).pos m
  · exact polyIdx_lt W ((natDegree_lt_iff_degree_lt h0).mpr hW)

/-- The index scramble is the reordering `v ↦ ι(U · idxPoly(v))` of the original sequence. -/
theorem seqPoint_idxScr (C : Gen s (ZMod p)) (U : ℕ → ℕ → ZMod p) (v : ℕ) :
    seqPoint (zcode p) (idxScr C U) v = seqPoint (zcode p) C (polyIdx p (uMul U (idxPolyP p v))) := by
  rw [seqPoint_eq_linPt, seqPoint_eq_linPt]
  funext c
  unfold linPt
  rw [idxPolyP_polyIdx]
  simp_rw [genY_idxScr]

/-- **`rem:randomize`(b), index scrambles**: for `U` upper triangular with nonzero diagonal (one `U` for all
coordinates, Faure–Tezuka), every prefix `P_m` of `C U` is the same set as the prefix `P_m` of `C`. -/
theorem idxScr_prefix (C : Gen s (ZMod p)) (U : ℕ → ℕ → ZMod p) (hU : ∀ k, U k k ≠ 0) (m : ℕ) :
    (∀ v, v < p ^ m → ∃ v', v' < p ^ m ∧ seqPoint (zcode p) (idxScr C U) v' = seqPoint (zcode p) C v) ∧
    (∀ v', v' < p ^ m → ∃ v, v < p ^ m ∧ seqPoint (zcode p) (idxScr C U) v' = seqPoint (zcode p) C v) := by
  refine ⟨fun v hv => ?_, fun v' hv' => ?_⟩
  · obtain ⟨V, hV, hUV⟩ := uMul_surj U hU m (idxPolyP p v) (idxPolyP_degree_lt v m hv)
    refine ⟨polyIdx p V, polyIdx_lt_of_degree V m hV, ?_⟩
    rw [seqPoint_idxScr, idxPolyP_polyIdx, hUV, polyIdx_idxPolyP]
  · exact ⟨_, polyIdx_lt_of_degree _ m (uMul_degree U _ m (idxPolyP_degree_lt v' m hv')), seqPoint_idxScr C U v'⟩

/-- **`rem:randomize`(b), index scrambles**: if the generator-matrix sequence `C` has close pairs (as every sequence
covered by `thm:nonqu`), its index scramble `C U` (`U` upper triangular, nonzero diagonal) is not quasi-uniform. -/
theorem idxScr_not_qu (hs : 1 ≤ s) (C : Gen s (ZMod p)) (U : ℕ → ℕ → ZMod p) (hU : ∀ k, U k k ≠ 0)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (seqPoint (zcode p) C v) (seqPoint (zcode p) C w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (seqPoint (zcode p) (idxScr C U)) := by
  have hfun : seqPoint (zcode p) (idxScr C U) =
      seqPoint (zcode p) C ∘ fun v => polyIdx p (uMul U (idxPolyP p v)) := funext (seqPoint_idxScr C U)
  rw [hfun]
  refine not_qu_comp (Fact.out : p.Prime).two_le hs _ (fun v c => ?_) _ (fun m v hv => ?_) hclose
  · rw [seqPoint_eq_linPt]; exact linPt_mem _ v c
  · obtain ⟨V, hV, hUV⟩ := uMul_surj U hU m (idxPolyP p v) (idxPolyP_degree_lt v m hv)
    exact ⟨polyIdx p V, polyIdx_lt_of_degree V m hV, by rw [idxPolyP_polyIdx, hUV, polyIdx_idxPolyP]⟩

end IdxPrime

end GeoSeq
