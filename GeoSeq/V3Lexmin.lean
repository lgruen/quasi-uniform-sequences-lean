/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Cap

@[expose] public section

/-!
# GeoSeq stage V3: the minimum for ordered windows (`prop:lexmin`)

`lexmin`: for `s = 3` and `p ∈ {5, 7}`, no ordered window system — in any order `π` of the coordinates
(`W_{π i ← π j}` = the windows of `def:lex` at positions `i, j`) — over a frame of distinct places
(`θ ≠ 0`, `λ_c ≠ 0`) satisfying (i) and (ii) of `prop:steer` has a positive window bound. Proof as in the
paper: `rem:lexexact` (`lex_exact_row`, transported along `π` by `winLB_perm`) forces `A_c + M_c + B_c ≤ p - 1`;
(i) forces every upper `B_{c←c'} ≥ 1` (the crosses are nonzero); at `p = 7` the covering (ii) of column `π 1`
with `κ_{π0←π1} = ±1` needs `M_1 ≥ 5`, while row `1` allows `M_1 ≤ 4` (a finite check in `𝔽_7`).
-/

namespace GeoSeq

open Finset

/-- `WinLB` is invariant under relabelling the coordinates. -/
theorem winLB_perm {s p : ℕ} [NeZero p] (W : Fin s → Fin s → Set (ZMod p)) (π : Equiv.Perm (Fin s))
    (LB : ℝ) (h : WinLB p W LB) : WinLB p (fun i j => W (π i) (π j)) LB := by
  intro e he hne σ hσ
  have hsum : ∀ f : Fin s → ℝ, ∑ c, f (π.symm c) = ∑ j, f j := fun f => Equiv.sum_comp π.symm f
  have key := h (e ∘ π.symm) (fun c => he _) (by obtain ⟨c, hc⟩ := hne; exact ⟨π c, by simpa using hc⟩)
    (σ ∘ π.symm) (fun c => by
      obtain ⟨x, hx, hxs⟩ := hσ (π.symm c)
      refine ⟨x ∘ π.symm, fun c' hc' => ?_, ?_⟩
      · have := hx (π.symm c') hc'
        simpa using this
      · simp only [Function.comp_apply]
        rw [hxs]
        exact (Equiv.sum_comp π.symm (fun j => (e j : ZMod p) * x j)).symm)
  simp only [Function.comp_apply] at key
  rwa [hsum (fun j => ((gapNum1 p (e j) (σ j) : ℝ) / p) ^ 2)] at key

/-- The depth-zero crosses of a frame of distinct places with `θ ≠ 0`, `λ_c ≠ 0` are nonzero. -/
theorem kapL_ne_zero {F : Type*} [Field F] {s : ℕ} (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (hθ : θ ≠ 0) (hlam : ∀ c, lamv c ≠ 0) (c c' : Fin s)
    (hcc : c ≠ c') : kapL θ lamv zθ c c' ≠ 0 := by
  unfold kapL
  refine div_ne_zero (mul_ne_zero hθ (hlam c)) (mul_ne_zero (mul_ne_zero (hlam c')
    (placeDer_ne_zero zθ hinj c)) (sub_ne_zero.mpr fun h => hcc (hinj h).symm))

lemma intWin_zero_zero {p : ℕ} {x : ZMod p} (hx : x ∈ intWin p (-(0 : ℕ) : ℤ) (0 : ℕ)) : x = 0 := by
  obtain ⟨z, h1, h2, rfl⟩ := hx
  have : z = 0 := by push_cast at h1 h2; omega
  simp [this]

/-- The finite check of `prop:lexmin` at `p = 7` (`decide +kernel`): if `κ = ∓1` (`z = -κ ∈ {-1, 0, 1}`,
`κ ≠ 0`), then for every `A_1 ≤ 6` some `β_0` is missed by every line of column `1` whose own value runs over
`M_1 ≤ 4` consecutive values `[-A_1-3, -A_1]` (with `β_1 = 0`) and whose row-`0` value must land in `[-1, 1]`. -/
theorem lexmin_check7 : ∀ κ : ZMod 7, ∀ z ∈ Finset.Icc (-1 : ℤ) 1, (z : ZMod 7) = -κ → κ ≠ 0 →
    ∀ a ∈ Finset.range 7, ∃ β0 : ZMod 7, ∀ t : ZMod 7, ∀ z2 ∈ Finset.Icc (-(a : ℤ) - 3) (-(a : ℤ)),
      (z2 : ZMod 7) = 0 + t * 1 → ∀ z1 ∈ Finset.Icc (-1 : ℤ) 1, (z1 : ZMod 7) ≠ β0 + t * κ := by
  decide +kernel

/-- **`prop:lexmin`** (minimum for ordered windows). For `s = 3` and `p ∈ {5, 7}`: let `W` be an ordered window
system (`def:lex`, data `A`, `M`, `B` with `IsLexData`) in the order `π` of the coordinates
(`W_{π i ← π j} = lexWin … i j`), over a frame of distinct places with `θ ≠ 0` and `λ_c ≠ 0`, satisfying
(i) (`-κ_{c←c'} ∈ W_{c←c'}`) and (ii) (every column covers) of `prop:steer`. Then no `LB > 0` satisfies
`WinLB p W LB`: `LB(W) ≤ 0`. -/
theorem lexmin (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7) (π : Equiv.Perm (Fin 3))
    (A M : Fin 3 → ℕ) (Bx : Fin 3 → Fin 3 → ℕ) (hd : IsLexData p A M Bx)
    (W : Fin 3 → Fin 3 → Set (ZMod p)) (hW : ∀ i j, W (π i) (π j) = lexWin p A M Bx i j)
    (θ : ZMod p) (lamv : Fin 3 → ZMod p) (zθ : Fin 3 → PowerSeries (ZMod p))
    (hinj : Function.Injective (ssPlace zθ)) (hθ : θ ≠ 0) (hlam : ∀ c, lamv c ≠ 0)
    (hi : ∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ W c c')
    (hii : ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin W c')) :
    ¬ ∃ LB : ℝ, 0 < LB ∧ WinLB p W LB := by
  rintro ⟨LB, hLB0, hLB⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hW' : (fun i j => W (π i) (π j)) = lexWin p A M Bx := funext fun i => funext fun j => hW i j
  have hLB' : WinLB p (lexWin p A M Bx) LB := hW' ▸ winLB_perm W π LB hLB
  have hrow : ∀ c, A c + M c + lexB Bx c + 1 ≤ p := fun c => by
    have h := lex_exact_row p hp2 A M Bx hd LB hLB' c
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have : (0 : ℝ) < (p : ℝ) - A c - M c - lexB Bx c := by
      have := lt_of_lt_of_le hLB0 h
      rwa [lt_div_iff₀ hp0, zero_mul] at this
    have : ((A c + M c + lexB Bx c : ℕ) : ℝ) < p := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).mp this
    omega
  -- every upper cross window is at least `[-1, 1]`
  have hB1 : ∀ i j : Fin 3, i < j → 1 ≤ Bx i j := by
    intro i j hij
    by_contra h0
    have h0' : Bx i j = 0 := by omega
    have hmem := hi (π i) (π j) (fun h => (ne_of_lt hij) (π.injective h))
    rw [hW i j] at hmem
    unfold lexWin at hmem
    rw [if_neg (not_lt.mpr hij.le), if_pos hij, h0'] at hmem
    have := intWin_zero_zero hmem
    exact kapL_ne_zero θ lamv zθ hinj hθ hlam _ _ (fun h => (ne_of_lt hij) (π.injective h))
      (neg_eq_zero.mp this)
  have hd0 := hd 0
  have hd1 := hd 1
  have hb0 : lexB Bx 0 = Bx 0 1 + Bx 0 2 := by
    unfold lexB
    rw [show univ.filter (fun c' : Fin 3 => (0 : Fin 3) < c') = {1, 2} by decide]
    simp
  have hb1 : lexB Bx 1 = Bx 1 2 := by
    unfold lexB
    rw [show univ.filter (fun c' : Fin 3 => (1 : Fin 3) < c') = {2} by decide]
    simp
  have h01 := hB1 0 1 (by decide)
  have h02 := hB1 0 2 (by decide)
  have h12 := hB1 1 2 (by decide)
  have hr0 := hrow 0
  have hr1 := hrow 1
  rcases hp with h5 | h7
  · -- `p = 5`: row `0` alone
    rw [h5] at hr0; omega
  · -- `p = 7`: row `0` forces `B_{0←1} = 1`, row `1` forces `M_1 ≤ 4`, column `π 1` needs `M_1 ≥ 5`
    rw [h7] at hr0 hr1
    have hB01 : Bx 0 1 = 1 := by omega
    have hM1 : M 1 ≤ 4 := by omega
    have h01' : π 0 ≠ π 1 := fun h => absurd (π.injective h) (by decide)
    have hκ0 := kapL_ne_zero θ lamv zθ hinj hθ hlam _ _ h01'
    have hκW := hi (π 0) (π 1) h01'
    rw [hW 0 1] at hκW
    unfold lexWin at hκW
    rw [if_neg (by decide), if_pos (by decide), hB01] at hκW
    obtain ⟨z, hz1, hz2, hzκ⟩ := hκW
    have hz1' : -1 ≤ z := by simpa using hz1
    have hz2' : z ≤ 1 := by simpa using hz2
    have hA1 : A 1 < 7 := by omega
    subst h7
    obtain ⟨β0, hβ⟩ := lexmin_check7 _ z (Finset.mem_Icc.mpr ⟨hz1', hz2'⟩) hzκ hκ0 (A 1)
      (Finset.mem_range.mpr hA1)
    obtain ⟨t, ht⟩ := hii (π 1) (fun c => if c = π 0 then β0 else 0)
    have hc0 := ht (π 0)
    have hc1 := ht (π 1)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc0 hc1
    rw [if_pos trivial] at hc0
    rw [if_neg h01'.symm] at hc1
    unfold stAlpha at hc0 hc1
    rw [if_neg h01'] at hc0
    rw [if_pos rfl, hW 1 1] at hc1
    rw [hW 0 1] at hc0
    unfold lexWin at hc0 hc1
    rw [if_neg (by decide), if_pos (by decide), hB01] at hc0
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)] at hc1
    obtain ⟨z1, hz11, hz12, hz1e⟩ := hc0
    obtain ⟨z2, hz21, hz22, hz2e⟩ := hc1
    have hM1' := hd1.1
    have hw1 : -(A 1 : ℤ) - 3 ≤ z2 := by push_cast at hz21; omega
    have hw2 : z2 ≤ -(A 1 : ℤ) := hz22
    have hz11' : -1 ≤ z1 := by simpa using hz11
    have hz12' : z1 ≤ 1 := by simpa using hz12
    exact hβ t z2 (Finset.mem_Icc.mpr ⟨hw1, hw2⟩) hz2e z1 (Finset.mem_Icc.mpr ⟨hz11', hz12'⟩) hz1e

end GeoSeq
