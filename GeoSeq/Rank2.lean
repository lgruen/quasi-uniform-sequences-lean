/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.N1

@[expose] public section

/-!
# GeoSeq stage S10: the direction count (`cor:cover`, `prop:rank2`)

* **`cover`** (`cor:cover`): if every line `β + F α` (`α ≠ 0`) meets `W ⊆ F^s`, the projection of `W` onto
  `F^s / Fα` is onto, and `|W| ≥ q^{s-1}`.
* `law_coef_exists`: for any digital sequence whose prefix `P_{sK}` is a net, every geometric digit
  `r_c = y_{c,K}` is a linear combination of the cell digits (a coefficient matrix `coef` exists).
* **`rank2`** (`prop:rank2`): for ANY such coefficient matrix and `K ≥ s - 1`, the minor of the cross rows
  of column `c'` on the `s - 1` finest digits of `c'` is nonzero. The formal proof is the semantic form of
  the paper's row exchange: a vector in the kernel of the minor gives an index vector whose digits vanish
  on the box `(K+1, …, K+1, K-s+1)` (a composition of `sK`), hence is `0` by the net property of `P_{sK}`.
* `rank2_indep`: the cross rows of column `c'` are linearly independent (rank `s - 1`), so in dimension
  three the two cross rows are not proportional.
-/

namespace GeoSeq

open Finset

section Cover

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

/-- **`cor:cover`** (covering in `F^{s-1}`): if every line `β + F α`, `α ≠ 0`, meets `W`, then the
projection of `W` along `α` onto `F^s / Fα` is onto, and `|W| ≥ q^{s-1}`. -/
theorem cover (α : Fin s → F) (hα : α ≠ 0) (W : Finset (Fin s → F))
    (hW : ∀ β : Fin s → F, ∃ t : F, β + t • α ∈ W) :
    (∀ y : (Fin s → F) ⧸ (Submodule.span F {α}), ∃ v ∈ W, Submodule.Quotient.mk v = y) ∧
      Fintype.card F ^ (s - 1) ≤ W.card := by
  have hsurj : ∀ y : (Fin s → F) ⧸ (Submodule.span F {α}), ∃ v ∈ W, Submodule.Quotient.mk v = y := by
    intro y
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨t, ht⟩ := hW β
    refine ⟨β + t • α, ht, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [add_sub_cancel_left]
    exact Submodule.smul_mem _ t (Submodule.subset_span rfl)
  refine ⟨hsurj, ?_⟩
  have hfin : Module.finrank F ((Fin s → F) ⧸ Submodule.span F {α}) = s - 1 := by
    have h := Submodule.finrank_quotient_add_finrank (Submodule.span F {α})
    rw [finrank_span_singleton hα, Module.finrank_fin_fun] at h
    omega
  have hcard : Nat.card ((Fin s → F) ⧸ Submodule.span F {α}) = Fintype.card F ^ (s - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := F), hfin, Nat.card_eq_fintype_card]
  rw [← hcard]
  have : Nat.card ((Fin s → F) ⧸ Submodule.span F {α}) ≤ Nat.card W := by
    refine Nat.card_le_card_of_surjective (fun v : W => Submodule.Quotient.mk (v : Fin s → F)) ?_
    intro y
    obtain ⟨v, hv, rfl⟩ := hsurj y
    exact ⟨⟨v, hv⟩, rfl⟩
  simpa using this

end Cover

section Rank

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-- The unit cell vector `U_{c,j}` at level `K` (cells `e_{c,j}`), for any dimension. -/
noncomputable def unitCellG {s : ℕ} (D : DigitCode F q) (C : Gen s F) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) (c : Fin s) (j : ℕ) : Fin (s * K) → F :=
  (cell_existsUnique D C K hnet (fun c₁ j₁ => if c₁ = c ∧ j₁ = j then 1 else 0)).exists.choose

lemma unitCellG_spec {s : ℕ} (D : DigitCode F q) (C : Gen s F) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) (c : Fin s) (j : ℕ) (c₁ : Fin s) (j₁ : ℕ) (hj : j₁ < K) :
    vecDigit C (unitCellG D C K hnet c j) c₁ j₁ = if c₁ = c ∧ j₁ = j then 1 else 0 :=
  (cell_existsUnique D C K hnet (fun c₁ j₁ => if c₁ = c ∧ j₁ = j then 1 else 0)).exists.choose_spec
    c₁ j₁ hj

/-- **The law at level `K` is linear in the cells**: for any digital sequence whose prefix `P_{sK}` is a
net, there is a coefficient matrix with `r_c = y_{c,K} = ∑_{c'', j<K} coef c c'' j · y_{c'',j}`. -/
theorem law_coef_exists {s : ℕ} (D : DigitCode F q) (C : Gen s F) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) :
    ∃ coef : Fin s → Fin s → ℕ → F, ∀ V : Fin (s * K) → F, ∀ c,
      vecDigit C V c K = ∑ c'', ∑ j ∈ range K, coef c c'' j * vecDigit C V c'' j := by
  refine ⟨fun c c'' j => vecDigit C (unitCellG D C K hnet c'' j) c K, fun V c => ?_⟩
  set W : Fin (s * K) → F :=
    ∑ c'', ∑ j ∈ range K, vecDigit C V c'' j • unitCellG D C K hnet c'' j with hW
  have hcells : ∀ c₁ : Fin s, ∀ j₁ < K, vecDigit C (V - W) c₁ j₁ = 0 := by
    intro c₁ j₁ hj
    have hsub : V - W = V + (-1 : F) • W := by simp [sub_eq_add_neg]
    rw [hsub, vecDigit_add, vecDigit_smul, hW, vecDigit_sum]
    simp_rw [vecDigit_sum, vecDigit_smul, unitCellG_spec D C K hnet _ _ c₁ j₁ hj]
    rw [Finset.sum_eq_single c₁]
    · rw [Finset.sum_eq_single j₁]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.2 hj) h
    · intro b _ hb
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h0 : V - W = 0 := by
    obtain ⟨U, _, hU⟩ := cell_existsUnique D C K hnet (fun _ _ => (0 : F))
    exact (hU _ hcells).trans (hU 0 fun c₁ j _ => vecDigit_zero C c₁ j).symm
  conv_lhs => rw [sub_eq_zero.1 h0, hW]
  rw [vecDigit_sum]
  simp_rw [vecDigit_sum, vecDigit_smul]
  refine Finset.sum_congr rfl fun c'' _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`prop:rank2`** (rank of the cross responses): let `C` be a digital sequence over a finite field in
dimension `s = n + 1` whose prefix `P_{sK}` is a `(0,sK,s)`-net, `K ≥ s - 1`, and let `coef` express the
geometric digits through the cell digits. Then for every coordinate `c'`, the minor of the cross rows
`(coef c c' ·)_{c ≠ c'}` on the `s - 1` finest digits `y_{c',K-s+1}, …, y_{c',K-1}` is nonzero. -/
theorem rank2 {n : ℕ} (D : DigitCode F q) (C : Gen (n + 1) F) (K : ℕ) (hK : n ≤ K)
    (hnet : BlockNet0 D C ((n + 1) * K) 0) (coef : Fin (n + 1) → Fin (n + 1) → ℕ → F)
    (hcoef : ∀ V : Fin ((n + 1) * K) → F, ∀ c,
      vecDigit C V c K = ∑ c'', ∑ j ∈ range K, coef c c'' j * vecDigit C V c'' j)
    (c' : Fin (n + 1)) : (crossFin coef K c').det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  -- the cell pattern: `v` on the `n` finest digits of `c'`, zero elsewhere
  set T : Fin (n + 1) → ℕ → F := fun c j =>
    if h : c = c' ∧ K - n ≤ j ∧ j < K then v ⟨j - (K - n), by omega⟩ else 0 with hT
  obtain ⟨V, hV, -⟩ := cell_existsUnique D C K hnet T
  -- the geometric digits of the coordinates `c ≠ c'` vanish
  have hr : ∀ i : Fin n, vecDigit C V (c'.succAbove i) K = 0 := by
    intro i
    rw [hcoef V, Finset.sum_eq_single c']
    · have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, crossFin, Pi.zero_apply] at this
      refine Eq.trans ?_ this
      have hsplit : range K = (range (K - n)) ∪ (Finset.Ico (K - n) K) := by
        ext j; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_union (Finset.disjoint_left.2 fun j h1 h2 => by
        simp only [Finset.mem_range] at h1; simp only [Finset.mem_Ico] at h2; omega)]
      rw [Finset.sum_eq_zero (fun j hj => by
        rw [hV c' j (by have := Finset.mem_range.1 hj; omega)]
        simp only [hT]
        rw [dif_neg (by have := Finset.mem_range.1 hj; omega), mul_zero]), zero_add]
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show K - (K - n) = n by omega, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hV c' (K - n + j) (by omega)]
      simp only [hT]
      rw [dif_pos (by first | exact ⟨rfl, by omega, by omega⟩ | exact ⟨trivial, by omega, by omega⟩)]
      congr 2
      ext; simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hV b j (Finset.mem_range.1 hj)]
      simp only [hT]
      rw [dif_neg (by tauto), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- the box `(K+1, …, K+1, K-n)` of `P_{sK}`: `V` and `0` have the same (zero) digits
  set d : Fin (n + 1) → ℕ := fun c => if c = c' then K - n else K + 1 with hd
  have hdsum : ∑ c, d c = (n + 1) * K := by
    rw [Fintype.sum_eq_add_sum_compl c']
    simp only [hd, if_pos rfl]
    rw [Finset.sum_congr rfl (fun c hc => if_neg (Finset.mem_compl.1 hc |> fun h => by
      simpa using h)), Finset.sum_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
      smul_eq_mul]
    simp only [add_tsub_cancel_right]
    have : (n + 1) * K = K + n * K := by ring
    rw [this]
    have : n * (K + 1) = n * K + n := by ring
    omega
  obtain ⟨U, _, hU⟩ := box_existsUnique D C _ hnet d hdsum (fun _ _ => (0 : F))
  have hV0 : V = 0 := by
    refine (hU V fun c j hj => ?_).trans (hU 0 fun c j _ => vecDigit_zero C c j).symm
    by_cases hc : c = c'
    · subst hc
      simp only [hd, if_pos rfl] at hj
      rw [hV c j (by omega)]
      simp only [hT]
      rw [dif_neg (by omega)]
    · simp only [hd, if_neg hc] at hj
      rcases Nat.lt_or_ge j K with hjK | hjK
      · rw [hV c j hjK]; simp only [hT]; rw [dif_neg (by tauto)]
      · have hjK' : j = K := by omega
        subst hjK'
        obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hc
        exact hr i
  apply hv0
  funext j
  have := hV c' (K - n + j) (by omega)
  rw [hV0, vecDigit_zero] at this
  simp only [hT] at this
  rw [dif_pos (by first | exact ⟨rfl, by omega, by omega⟩ | exact ⟨trivial, by omega, by omega⟩)] at this
  have e : (⟨K - n + (j : ℕ) - (K - n), by omega⟩ : Fin n) = j := by ext; simp
  rw [e] at this
  exact this.symm

/-- **`prop:rank2`, "in particular"**: the `s - 1` cross rows `j ↦ coef c j` (`c ≠ c'`, `j < K`) of column
`c'` are linearly independent, i.e. the cross matrix `X_{c'}` has rank `s - 1`; in dimension three
(`n = 2`) the two cross rows of a column are not proportional. -/
theorem rank2_indep {n : ℕ} (D : DigitCode F q) (C : Gen (n + 1) F) (K : ℕ) (hK : n ≤ K)
    (hnet : BlockNet0 D C ((n + 1) * K) 0) (coef : Fin (n + 1) → Fin (n + 1) → ℕ → F)
    (hcoef : ∀ V : Fin ((n + 1) * K) → F, ∀ c,
      vecDigit C V c K = ∑ c'', ∑ j ∈ range K, coef c c'' j * vecDigit C V c'' j)
    (c' : Fin (n + 1)) :
    LinearIndependent F (fun i : Fin n => fun j : Fin K => coef (c'.succAbove i) c' j) := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero (rank2 D C K hK hnet coef hcoef c')
  let f : (Fin K → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun r j => r ⟨K - n + j, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearIndependent.of_comp f ?_
  convert h using 1
  funext i; funext j; rfl

end Rank

end GeoSeq
