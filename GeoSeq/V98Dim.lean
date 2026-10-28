/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Rel

@[expose] public section

/-!
# GeoSeq stage V9-8 (part 6): the dimension of the relation spaces (`lem:reltype`, last sentence)

* `suppEquiv`: the families of top index `T` (`relSpace a L T 0`, no condition) are `F^{s × (T+1)}`.
* **`reltype_poly_surj`**: every polynomial of degree `< s(T+1)` is the polynomial of exactly one family of top index
  `T` (injective linear map between spaces of equal dimension).
* **`reltype_dim`** (`lem:reltype`): the relations of top index `T` on `P_m` form a space of dimension `s(T+1) - m`
  (`m ≤ s(T+1)`): `s` on the full level `P_{sT}`, `1` on `P_{s(T+1)-1}`.
-/

namespace GeoSeq

open Finset Polynomial Module

section Dim
variable {F : Type*} [Field F] {s : ℕ}

/-- The families of top index `T` are the vectors `F^{s × (T+1)}`. -/
noncomputable def suppEquiv (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) :
    relSpace a L T 0 ≃ₗ[F] (Fin s → Fin (T + 1) → F) where
  toFun f := fun c k => f.1 c k
  invFun g := ⟨fun c n => if h : n < T + 1 then g c ⟨n, h⟩ else 0,
    fun c n hn => by simp only; rw [dif_neg (by omega)], fun V hV => absurd hV (Nat.not_lt_zero _)⟩
  map_add' f g := rfl
  map_smul' r f := rfl
  left_inv f := by
    apply Subtype.ext; funext c n
    simp only
    split_ifs with h
    · rfl
    · exact (f.2.1 c n (by omega)).symm
  right_inv g := by funext c k; simp [k.2]

lemma finrank_supp (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) :
    finrank F (relSpace a L T 0) = s * (T + 1) := by
  rw [(suppEquiv a L T).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The polynomial of a family of top index `T`, as a linear map into `F[X]_{< s(T+1)}`. -/
noncomputable def relPolyLin (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) :
    relSpace a L T 0 →ₗ[F] degreeLT F (s * (T + 1)) where
  toFun f := ⟨relPoly a L f.1 T, by
    rw [mem_degreeLT]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; simp [relPoly]
    · refine lt_of_le_of_lt degree_le_natDegree ?_
      have := natDegree_relPoly a L f.1 T
      have : 1 ≤ s * (T + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast (show (relPoly a L f.1 T).natDegree < s * (T + 1) by omega)⟩
  map_add' f g := Subtype.ext (relPoly_add a L f.1 g.1 T)
  map_smul' r f := Subtype.ext (by simp only [SetLike.val_smul, relPoly_smul, smul_eq_C_mul, RingHom.id_apply])

lemma relPolyLin_bij (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (T : ℕ) : Function.Bijective (relPolyLin a L T) := by
  have hinj : Function.Injective (relPolyLin a L T) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h0 : relPoly a L f.1 T = 0 := congrArg Subtype.val hf
    exact Subtype.ext ((relPoly_eq_zero_iff a ha L hL f.1 T f.2.1).mp h0)
  have : FiniteDimensional F (relSpace a L T 0) := LinearEquiv.finiteDimensional (suppEquiv a L T).symm
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [finrank_supp, (degreeLTEquiv F _).finrank_eq, Module.finrank_fin_fun]

/-- **`lem:reltype`, converse**: every polynomial `B` of degree `< s(T+1)` is the polynomial of exactly one family of
top index `T`. -/
theorem reltype_poly_surj (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (T : ℕ) (B : F[X]) (hB : B.degree < ((s * (T + 1) : ℕ) : WithBot ℕ)) :
    ∃! f : Fin s → ℕ → F, (∀ c n, T < n → f c n = 0) ∧ relPoly a L f T = B := by
  obtain ⟨f, hf⟩ := (relPolyLin_bij a ha L hL T).2 ⟨B, mem_degreeLT.mpr hB⟩
  refine ⟨f.1, ⟨f.2.1, congrArg Subtype.val hf⟩, fun g ⟨hg1, hg2⟩ => ?_⟩
  have hgm : g ∈ relSpace a L T 0 := ⟨hg1, fun V hV => absurd hV (Nat.not_lt_zero _)⟩
  have := (relPolyLin_bij a ha L hL T).1 (a₁ := ⟨g, hgm⟩) (a₂ := f) (Subtype.ext (by
    show relPoly a L g T = relPoly a L f.1 T
    rw [hg2]; exact (congrArg Subtype.val hf).symm))
  exact congrArg Subtype.val this

/-- **`lem:reltype`** (dimension): the relations of top index `T` on `P_m` (with `0`) form a space
of dimension `s(T+1) - m` (truncated subtraction: `0` for `m ≥ s(T+1)`). -/
theorem reltype_dim (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (T m : ℕ) : finrank F (relSpace a L T m) = s * (T + 1) - m := by
  let φ : relSpace a L T m →ₗ[F] degreeLT F (s * (T + 1) - m) :=
    { toFun := fun f => ⟨relPoly a L f.1 T, mem_degreeLT.mpr (relPoly_degree_lt a ha L f.1 T m f.2)⟩
      map_add' := fun f g => Subtype.ext (relPoly_add a L f.1 g.1 T)
      map_smul' := fun r f => Subtype.ext (by
        simp only [SetLike.val_smul, relPoly_smul, smul_eq_C_mul, RingHom.id_apply]) }
  have hbij : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      have h0 : relPoly a L f.1 T = 0 := congrArg Subtype.val hf
      exact Subtype.ext ((relPoly_eq_zero_iff a ha L hL f.1 T f.2.1).mp h0)
    · rintro ⟨B, hB⟩
      have hB' := mem_degreeLT.mp hB
      obtain ⟨f, ⟨hf1, hf2⟩, -⟩ := reltype_poly_surj a ha L hL T B
        (lt_of_lt_of_le hB' (by exact_mod_cast Nat.sub_le _ _))
      refine ⟨⟨f, relSpace_of_degree a ha L f T m hf1 (by rw [hf2]; exact hB')⟩, Subtype.ext ?_⟩
      exact hf2
  rw [(LinearEquiv.ofBijective φ hbij).finrank_eq, (degreeLTEquiv F _).finrank_eq, Module.finrank_fin_fun]

end Dim

end GeoSeq
