/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V94Seq
public import GeoSeq.V9QU
public import GeoSeq.Mesh
public import GeoSeq.Law
public import GeoSeq.OneDigit

@[expose] public section

/-!
# GeoSeq stage V9-4 (part 2): `thm:residuestar`

* `resStar_carry`: the row `c⋆` of the one-digit carry response of `𝓡^⋆_v` at every level `K` and carry length
  `l`: `X^{(l)}_{c⋆←c} = k_c` (`c ≠ c⋆`), `O^{(l)}_{c⋆} = 0` (from `lem:residuestar-rel`; the other rows are not
  needed).
* `cert_row` (the one-row certificate of `LEAN_PLAN_V4` §2.5): `lem:cert` with `j = 1` keeping only the term of
  one coordinate; the other rows of the carry response exist by the net property (`carry_exists`) and do not enter.
* `gap_cabs`, `gapNum1_step_zero`: `f_1(e, σ) ≥ (|σ|_∘ - 1)/p` for `e ∈ {-1,0,1}`, and `f_1(±1, 0) = (p-1)/p`.
* **`residuestar_sep`** (`thm:residuestar`): `sep(P_{sK}) ≥ β(k)` for every `K ≥ 1` (`p ≥ 5`).
* `residuestar_allN`, `residuestar_mesh`, `residuestar_qu` (`thm:residuestar`, last sentence): for `β(k) > 0`,
  `δ(P_{[N]}) ≥ (β(k)/p) N^{-1/s}` for every `N ≥ 2`, the mesh-ratio bound `h ≤ (√s p/β(k)) δ`, quasi-uniform.
-/

namespace GeoSeq

open Finset Polynomial

section Carry
variable {F : Type*} [Field F] {s : ℕ}

/-- **The carry response of the staggered coordinate** (`lem:residuestar-rel`, prime-base reading): at every
level `K ≥ 1` and carry length `1 ≤ l ≤ K`, the one-digit response `D(l)[c⋆][c']` is `k_{c'}` for `c' ≠ c⋆` and `0`
for `c' = c⋆` (constant responses `X^{(l)}_{c⋆←c'} = k_{c'}`, `O^{(l)}_{c⋆} = 0`). -/
theorem resStar_carry {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hnet : BlockNet0 D (resStar a θ cs μs k) (s * K) 0) (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K)
    (c' : Fin s) :
    IsCarryEntry (resStar a θ cs μs k) K 0 l cs c' (if c' = cs then 0 else k c') := by
  obtain ⟨d, hd⟩ := carry_exists D (resStar a θ cs μs k) K hnet 0 l cs c'
  suffices h : d = (if c' = cs then 0 else k c') by rw [← h]; exact hd
  obtain ⟨V, hV⟩ := hd.1
  rw [← hd.2 V hV, add_zero]
  set f : ℕ → F := fun j => if h : j < s * K then V ⟨j, h⟩ else 0 with hf
  have hvd : ∀ c n, vecDigit (resStar a θ cs μs k) V c n =
      ∑ j ∈ range (s * K), resStar a θ cs μs k c n j * f j := by
    intro c n
    rw [vecDigit, ← Fin.sum_univ_eq_sum_range (fun j => resStar a θ cs μs k c n j * f j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hf, j.isLt]
  rw [hvd, resStar_rel a ha θ cs μs k hk K hK f _ le_rfl]
  have hc : ∀ c ∈ univ.erase cs, k c * ∑ j ∈ range (s * K), resStar a θ cs μs k c (K - 1) j * f j =
      if c' = c then k c' else 0 := by
    intro c _
    rw [← hvd, hV c (K - 1) (by omega), carryPat]
    by_cases h : c = c'
    · subst h; rw [if_pos ⟨rfl, by omega, by omega⟩, if_pos rfl, mul_one]
    · rw [if_neg (fun h' => h h'.1), if_neg (Ne.symm h), mul_zero]
  rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq]
  by_cases h : c' = cs
  · rw [if_neg (by simp [h]), if_pos h]
  · rw [if_pos (Finset.mem_erase.mpr ⟨h, mem_univ _⟩), if_neg h]

end Carry

section Cert
variable {s : ℕ}

/-- **The one-row certificate** (`lem:cert` with `j = 1`, keeping only the term of one coordinate `c₀`; plan
§2.5): if the prefix `P_{sK}` is a `(0, sK, s)`-net over `ℤ/qℤ` with `q^K ≥ 4`, `Drow l c' = D(l)[c₀][c']` is the
row `c₀` of the one-digit carry response (`1 ≤ l ≤ K`), and `LB ≤ f_1(e_{c₀}, σ_{c₀})` for every step,
`σ_{c₀} = ∑_{c'} e_{c'} D(l_{c'})[c₀][c']`, then `c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_row {q : ℕ} [NeZero q] (C : Gen s (ZMod q)) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (c₀ : Fin s) (Drow : ℕ → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c', IsCarryEntry C K 0 l c₀ c' (Drow l c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ (gapNum1 q (e c₀) (∑ c', (e c' : ZMod q) * Drow (l c') c') : ℝ) / q) :
    SepAtLevel q s K (seqPoint (zcode q) C) (min 1 LB) := by
  classical
  let Dr : ℕ → Fin s → Fin s → ZMod q := fun l c c' =>
    if c = c₀ then Drow l c' else
      if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists (zcode q) C K hnet 0 l c c') else 0
  have hDr : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c') := by
    intro l h1 h2 c c'
    by_cases hc : c = c₀
    · subst hc; simp only [Dr, if_pos rfl]; exact hD l h1 h2 c'
    · simp only [Dr, if_neg hc, And.intro h1 h2, and_self, dite_true]
      exact Classical.choose_spec (carry_exists (zcode q) C K hnet 0 l c c')
  refine cert_one C K hK hnet Dr hDr LB fun e l hst => ?_
  have hrow : ∑ c', (e c' : ZMod q) * Dr (l c') c₀ c' = ∑ c', (e c' : ZMod q) * Drow (l c') c' := by
    simp only [Dr, if_pos rfl]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine (hLB e l hst).trans ?_
  rw [← hrow]
  set g := fun c => (gapNum1 q (e c) (∑ c', (e c' : ZMod q) * Dr (l c') c c') : ℝ) / q
  have hg0 : 0 ≤ g c₀ := div_nonneg (Nat.cast_nonneg _) hq
  calc g c₀ = Real.sqrt (g c₀ ^ 2) := (Real.sqrt_sq hg0).symm
    _ ≤ Real.sqrt (∑ c, g c ^ 2) := Real.sqrt_le_sqrt
        (Finset.single_le_sum (f := fun c => g c ^ 2) (fun c _ => sq_nonneg _) (mem_univ c₀))

lemma cabsZ_zero (p : ℕ) : cabsZ (0 : ZMod p) = 0 := by simp [cabsZ]

lemma two_cabsZ_le {p : ℕ} [NeZero p] (x : ZMod p) : 2 * cabsZ x ≤ p := by
  have := ZMod.val_lt x; unfold cabsZ; omega

/-- `f_1(e, σ) ≥ (|σ|_∘ - 1)/p` for `e ∈ {-1, 0, 1}` (numerators). -/
lemma gap_cabs (p : ℕ) [NeZero p] (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (σ : ZMod p) :
    cabsZ σ ≤ gapNum1 p e σ + 1 := by
  by_cases hσ : σ = 0
  · subst hσ; rw [cabsZ_zero]; omega
  · rw [gapNum1_eq p e σ hσ]
    have hv := ZMod.val_lt σ
    unfold cabsZ
    obtain ⟨h1, h2⟩ := he
    have : e = -1 ∨ e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl | rfl <;> omega

/-- `f_1(±1, 0) = (p-1)/p` (numerators). -/
lemma gapNum1_step_zero (p : ℕ) [NeZero p] (e : ℤ) (he : e = 1 ∨ e = -1) :
    gapNum1 p e 0 = p - 1 := by
  rw [gapNum1_zero]; rcases he with rfl | rfl <;> simp

lemma starStep_nonempty (hs : 2 ≤ s) (cs : Fin s) : ∃ e, StarStep cs e := by
  obtain ⟨c0, hc0⟩ : ∃ c0 : Fin s, c0 ≠ cs := by
    by_cases h : (cs : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [Fin.ext_iff] at e; simp at e; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [Fin.ext_iff] at e; simp at e; omega⟩
  refine ⟨fun c => if c = c0 then 1 else 0, fun c => by dsimp only; split_ifs <;> norm_num, by simp [Ne.symm hc0],
    c0, by simp⟩

lemma betaStar_bdd (p : ℕ) (cs : Fin s) (k : Fin s → ZMod p) :
    BddBelow (Set.range fun e : {e : Fin s → ℤ // StarStep cs e} =>
      ((cabsZ (∑ c, (e.1 c : ZMod p) * k c) : ℝ) - 1) / p) := by
  refine ⟨-1 / p, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact div_le_div_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) (cabsZ (∑ c, (e.1 c : ZMod p) * k c)); linarith)
    (Nat.cast_nonneg p)

/-- `β(k) ≤ (|k · e'|_∘ - 1)/p` for every step `e'`. -/
lemma betaStar_le (p : ℕ) (cs : Fin s) (k : Fin s → ZMod p) (e : Fin s → ℤ) (he : StarStep cs e) :
    betaStar p cs k ≤ ((cabsZ (∑ c, (e c : ZMod p) * k c) : ℝ) - 1) / p :=
  ciInf_le (betaStar_bdd p cs k) ⟨e, he⟩

/-- `L ≤ β(k)` as soon as `L ≤ (|k · e'|_∘ - 1)/p` for every step `e'` (`s ≥ 2`). -/
lemma le_betaStar (p : ℕ) (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) (L : ℝ)
    (h : ∀ e, StarStep cs e → L ≤ ((cabsZ (∑ c, (e c : ZMod p) * k c) : ℝ) - 1) / p) :
    L ≤ betaStar p cs k := by
  obtain ⟨e0, he0⟩ := starStep_nonempty hs cs
  have : Nonempty {e : Fin s → ℤ // StarStep cs e} := ⟨⟨e0, he0⟩⟩
  exact le_ciInf fun e => h e.1 e.2

lemma betaStar_le_pred (p : ℕ) [NeZero p] (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) :
    betaStar p cs k ≤ ((p : ℝ) - 1) / p := by
  obtain ⟨e0, he0⟩ := starStep_nonempty hs cs
  refine (betaStar_le p cs k e0 he0).trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg p))
  have h2 := two_cabsZ_le (∑ c, (e0 c : ZMod p) * k c)
  have : (cabsZ (∑ c, (e0 c : ZMod p) * k c) : ℝ) ≤ p := by exact_mod_cast (by omega : _ ≤ p)
  linarith

variable {p : ℕ} [Fact p.Prime]

/-- **`thm:residuestar`** (separation): for a prime `p ≥ 5`, distinct places, `θ, μ⋆ ≠ 0` and nonzero weights,
`sep(P_{sK}) ≥ β(k)` for every `K ≥ 1`. -/
theorem residuestar_sep (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p s K (seqPoint (zcode p) (resStar a θ cs μs k)) (betaStar p cs k) := by
  classical
  have hnet : BlockNet0 (zcode p) (resStar a θ cs μs k) (s * K) 0 :=
    resStar_t0 (zcode p) a ha θ hθ cs μs hμ k hk (s * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hβp := betaStar_le_pred p hs cs k
  have hβ1 : betaStar p cs k ≤ 1 := hβp.trans (by rw [div_le_one hp0]; linarith)
  have h := cert_row (resStar a θ cs μs k) K hq hnet cs (fun _ c' => if c' = cs then 0 else k c')
    (fun l hl hlK c' => resStar_carry (zcode p) a ha θ cs μs k hk K hK hnet l hl hlK c')
    (betaStar p cs k) ?_
  · rwa [min_eq_right hβ1] at h
  rintro e l ⟨he, hne, -⟩
  set e' : Fin s → ℤ := fun c => if c = cs then 0 else e c with he'
  have hσ : ∑ c', (e c' : ZMod p) * (if c' = cs then 0 else k c') = ∑ c, (e' c : ZMod p) * k c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = cs <;> simp [he', h]
  rw [hσ]
  by_cases hE : ∃ c, e' c ≠ 0
  · have hst : StarStep cs e' := ⟨fun c => by by_cases h : c = cs <;> simp [he', h, he c],
      by simp [he'], hE⟩
    refine (betaStar_le p cs k e' hst).trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg p))
    have := gap_cabs p (e cs) (he cs) (∑ c, (e' c : ZMod p) * k c)
    have : (cabsZ (∑ c, (e' c : ZMod p) * k c) : ℝ) ≤ gapNum1 p (e cs) (∑ c, (e' c : ZMod p) * k c) + 1 := by
      exact_mod_cast this
    linarith
  · push_neg at hE
    have hz : ∑ c, (e' c : ZMod p) * k c = 0 := Finset.sum_eq_zero fun c _ => by rw [hE c]; simp
    obtain ⟨c1, hc1⟩ := hne
    have hc1s : c1 = cs := by
      by_contra h; exact hc1 (by have := hE c1; simpa [he', h] using this)
    subst hc1s
    have hes : e c1 = 1 ∨ e c1 = -1 := by have := he c1; omega
    rw [hz, gapNum1_step_zero p _ hes]
    refine hβp.trans (le_of_eq ?_)
    rw [Nat.cast_sub (by omega)]; norm_num

/-- **`thm:residuestar`** (all `N`): if `β(k) ≥ 0`, then `δ(P_{[N]}) ≥ (β(k)/p) N^{-1/s}` for every `N ≥ 2`. -/
theorem residuestar_allN (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (hβ : 0 ≤ betaStar p cs k) :
    SepAllN s (seqPoint (zcode p) (resStar a θ cs μs k)) (betaStar p cs k / p) :=
  prefix_sep p s (by omega) (by omega) _ _ hβ
    (fun K hK => residuestar_sep hp hs a ha θ hθ cs μs hμ k hk K hK)

/-- **`thm:residuestar`** (mesh ratio): if `β(k) > 0`, then `h(P_{[N]}) ≤ (√s p / β(k)) δ(P_{[N]})` for every
`N ≥ 2` (`δ` toroidal, `2 · sepRad`). -/
theorem residuestar_mesh (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (hβ : 0 < betaStar p cs k) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (resStar a θ cs μs k))) ≤
      Real.sqrt s * p / betaStar p cs k *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
          (prefixSet N (seqPoint (zcode p) (resStar a θ cs μs k)))) :=
  prefix_mesh (zcode p) _ (by omega) (by omega) (resStar_t0 (zcode p) a ha θ hθ cs μs hμ k hk) _ hβ
    (fun K hK => residuestar_sep hp hs a ha θ hθ cs μs hμ k hk K hK) N hN

/-- **`thm:residuestar`** (quasi-uniformity): if `β(k) > 0`, the staggered residue sequence is quasi-uniform. -/
theorem residuestar_qu (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (hβ : 0 < betaStar p cs k) :
    IsQuasiUniform (seqPoint (zcode p) (resStar a θ cs μs k)) :=
  qu_of_sepAllN (zcode p) _ (by omega) (by omega) (resStar_t0 (zcode p) a ha θ hθ cs μs hμ k hk) _
    (div_pos hβ (by exact_mod_cast (show 0 < p by omega)))
    (residuestar_allN hp hs a ha θ hθ cs μs hμ k hk hβ.le)

end Cert

end GeoSeq
