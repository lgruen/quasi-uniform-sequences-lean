/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4Trans
public import GeoSeq.V10_1Blk
public import GeoSeq.V10_1Sign

@[expose] public section

/-!
# GeoSeq stage V10-4 (part 3): `thm:block`(c) for every `s ≥ 3`

* `ustar_hrel`, `ustar_hNd`: identity (a) of `def:block` and the vanishing orders for the design numerators
  `ustarNd` of `U*_s` (from `ustar_reachable` and `designNum_exists`, `designNum_order`), every prime `p ≥ s`.
* `aStar_ge`: `a*_s ≥ s - 1` (every level-`0` column of `U*_s` has no zero entry), so `p ≥ 5 a*_s + 4` implies `p ≥ s`.
* **`blkS_block`** (`thm:block`(c), every `s ≥ 3`, the written range): for every prime `p ≥ 5 a*_s + 4` and `θ ≠ 0`,
  `blkS s θ` is a digital `(0,s)`-sequence, the geometric digits follow `U*_s` at every `P_{s²K}`, and
  `sep(P_{s²K}) ≥ 1 - (a*_s+1)/p` (diagonal dominance, `dom_LB`).
* `ustar_col0`: the column of the place `0` (the nets' place `∞`) of `F_0` is `(·, 1, …, 1)` (`E_{∞,0} = (0,1,…,1)`,
  `γ_0 = 1`), for every `s ≥ 3`; hence **`blkS_LB_eq_of`**: `LB(F) = 1 - (a*_s+1)/p` exactly when the row of the place
  `0` has the largest `α` (`α_0 = a*_s`; the paper checks this by exact computation for `s ≤ 10`).
* **The free diagonal, every `s`** (`blkSd_block`, `blkSd_block_sc`): the off-diagonal entries of `U*_s` with ANY
  diagonal `F_0[c][c] = -δ_c` give a `(0,s)`-sequence with the design relation and `sep(P_{s²K}) ≥ min(1, LB)` for every
  lower bound of the one-digit relaxation; with the sign-class condition (`SignClass`) at level `A`,
  `sep(P_{s²K}) ≥ 1 - (A+1)/p` for every prime past the threshold of `sc_LB`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ## Identity (a) and the vanishing orders for `U*_s` -/

lemma ustarNd_spec {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c : Fin s) :
    IdA (ustarA (p := p) s) (ustarV s) (ustarFd s) c (fun n => ustarNd s c (s - 1 - n)) ∧
      ∀ n, n + 2 ≤ s → ∃ N', ustarNd (p := p) s c (s - 1 - n) = (X - C (ustarA s c)) ^ n * N' ∧
        N'.eval (ustarA s c) ≠ 0 := by
  classical
  obtain ⟨γ, hR⟩ := ustar_reachable (p := p) hs hsp
  have ha := ustarA_injective (p := p) hsp
  have hv := ustarV_ne (p := p) hsp
  have hex : ∃ N : ℕ → (ZMod p)[X], IdA (ustarA s) (ustarV s) (ustarFd s) c N :=
    (designNum_exists (by omega) _ ha _ hv _ γ hR c).imp fun N h => h.1
  have hN := Classical.choose_spec hex
  have hval : ∀ n, n + 2 ≤ s → ustarNd (p := p) s c (s - 1 - n) = Classical.choose hex n := by
    intro n hn
    simp only [ustarNd, designNd, dif_pos hex]
    rw [show s - 1 - (s - 1 - n) = n by omega]
  refine ⟨fun i hic => ?_, fun n hn => ?_⟩
  · have hsum : ∑ n ∈ range (s - 1), C (ustarFd (p := p) s n i c) * Classical.choose hex n =
        ∑ n ∈ range (s - 1), C (ustarFd (p := p) s n i c) * ustarNd s c (s - 1 - n) :=
      Finset.sum_congr rfl (fun (n : ℕ) (hn : n ∈ range (s - 1)) => by
        rw [mem_range] at hn; rw [hval n (by omega)])
    rw [hN i hic, hsum]
  · rw [hval n hn]
    exact designNum_order (by omega) _ ha _ hv _ γ hR c _ hN n hn

/-- **Identity (a) of `def:block` for `thm:block`(c)**, every `s ≥ 3` and every prime `p ≥ s`. -/
theorem ustar_hrel {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c i : Fin s) (h : i ≠ c) :
    wCoCo (ustarA (p := p) s) c i = -C (ustarV s i) *
      ∑ n ∈ range (s - 1), C (ustarFd s n i c) * ustarNd s c (s - 1 - n) :=
  (ustarNd_spec hs hsp c).1 i h

/-- The vanishing orders of the design numerators of `thm:block`(c), every `s ≥ 3`, every prime `p ≥ s`. -/
theorem ustar_hNd {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c : Fin s) (n : ℕ) (hn : n + 2 ≤ s) :
    ∃ N', ustarNd (p := p) s c (s - 1 - n) = (X - C (ustarA s c)) ^ n * N' ∧ N'.eval (ustarA s c) ≠ 0 :=
  (ustarNd_spec hs hsp c).2 n hn

/-- **`def:block`(a), uniqueness for `thm:block`(c)**: every solution of identity (a) is `ustarNd`. -/
theorem ustar_Nd_unique {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (c : Fin s) (N : ℕ → (ZMod p)[X])
    (hN : IdA (ustarA s) (ustarV s) (ustarFd s) c N) (n : ℕ) (hn : n + 2 ≤ s) :
    N n = ustarNd s c (s - 1 - n) := by
  obtain ⟨γ, hR⟩ := ustar_reachable (p := p) hs hsp
  exact designNum_unique (by omega) _ (ustarA_injective hsp) _ (ustarV_ne hsp) _ γ hR c N _ hN
    (ustarNd_spec hs hsp c).1 n hn

/-! ## `a*_s ≥ s - 1` -/

lemma wQ_ne {s : ℕ} [NeZero s] {c d : Fin s} (hcd : c ≠ d) : Z3NetA.wQ c d ≠ 0 := by
  unfold Z3NetA.wQ Z3NetF.wN
  split_ifs with h
  · exact one_ne_zero
  · rw [Ring.inverse_eq_inv']
    refine inv_ne_zero (sub_ne_zero.mpr fun he => hcd ?_)
    simp only [Z3NetA.placeA, sub_left_inj, Nat.cast_inj] at he
    exact Fin.ext he

/-- Every entry of a level-`0` column of `U*_s` is nonzero. -/
lemma ustar_level0_ne {s : ℕ} [NeZero s] (hs : 3 ≤ s) {c d : Fin s} (hcd : c ≠ d) : Z3NetA.UstarF s 0 c d ≠ 0 := by
  obtain ⟨-, g, hg, -, hu, hrep⟩ := Z3NetA.Ustar_adm hs d 0 (by omega)
  have hrep' := hrep c hcd
  simp only [if_neg hcd] at hrep'
  have hM : Z3NetF.Msum (Z3NetA.UstarF s) 0 c d = Z3NetA.UstarF s 0 c d := by simp [Z3NetF.Msum]
  rw [hM] at hrep'
  intro h0
  rw [h0, Int.cast_zero, eq_C_of_natDegree_eq_zero hg, eval_C] at hrep'
  have hlc : g.coeff 0 ≠ 0 := by
    have := hu.1
    rwa [leadingCoeff, hg] at this
  exact mul_ne_zero (wQ_ne hcd) hlc hrep'.symm

/-- `a*_s ≥ s - 1`. -/
theorem aStar_ge {s : ℕ} [NeZero s] (hs : 3 ≤ s) : s - 1 ≤ Z3NetA.aStar s := by
  have h0 := (Z3NetA.Ustar_dominant hs (0 : Fin s)).2.2
  refine le_trans ?_ (h0.1.le.trans h0.2)
  calc s - 1 = ∑ d ∈ univ.filter (fun d : Fin s => d ≠ 0), 1 := by
        rw [sum_const, smul_eq_mul, mul_one, filter_ne' univ (0 : Fin s), card_erase_of_mem (mem_univ _),
          card_univ, Fintype.card_fin]
    _ ≤ _ := by
        refine sum_le_sum fun d hd => ?_
        rw [mem_filter] at hd
        refine le_trans ?_ (le_sup (f := fun j => (Z3NetF.Msum (Z3NetA.UstarF s) j 0 d).natAbs)
          (mem_range.mpr (show 0 < s - 1 by omega)))
        have : Z3NetF.Msum (Z3NetA.UstarF s) 0 0 d = Z3NetA.UstarF s 0 0 d := by simp [Z3NetF.Msum]
        simp only [this]
        exact Int.natAbs_pos.mpr (ustar_level0_ne hs (Ne.symm hd.2))

/-! ## The bound: diagonal dominance -/

/-- The bounds `B_{ic} = max_j |M^{(j)}[i][c]|` of `U*_s`. -/
noncomputable def ustarB (s : ℕ) [NeZero s] (i c : Fin s) : ℤ :=
  (((range (s - 1)).sup fun j => (Z3NetF.Msum (Z3NetA.UstarF s) j i c).natAbs : ℕ) : ℤ)

/-- **The written bound of `thm:block`(c), every `s ≥ 3`**: for every prime `p ≥ 5 a*_s + 4` every step has a term
`≥ 1 - (a*_s+1)/p`, i.e. `LB(F) ≥ 1 - (a*_s+1)/p` (diagonal dominance of `U*_s`, `dom_LB`). -/
theorem ustar_LB_proof {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hp : 5 * Z3NetA.aStar s + 4 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - Z3NetA.aStar s - 1) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2) := by
  have hdom := Z3NetA.Ustar_dominant hs
  refine dom_LB (by omega) (Z3NetA.UstarF s) (Z3NetF.Msum (Z3NetA.UstarF s)) (fun j _ i c => rfl)
    (fun i => (Z3NetA.alphaS i : ℤ)) (ustarB s) (Z3NetA.aStar s) ?_ ?_ ?_ ?_ hp K
  · intro j hj i
    simp only [Z3NetF.Msum]
    rw [sum_range_succ', sum_eq_zero fun n _ => (hdom i).2.1 (n + 1) (by omega), zero_add, (hdom i).1]
  · intro j hj i c _
    unfold ustarB
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le_sup (f := fun j => (Z3NetF.Msum (Z3NetA.UstarF s) j i c).natAbs)
      (mem_range.mpr (by omega))
  · intro i
    have h := (hdom i).2.2.1
    rw [filter_ne' univ i] at h
    unfold ustarB
    exact_mod_cast h.le
  · intro i
    exact_mod_cast (hdom i).2.2.2

/-- **`thm:block`(c) for every `s ≥ 3`** (the written range): for every prime `p ≥ 5 a*_s + 4` and `θ ≠ 0`, the
block-periodic residue sequence with the design `U*_s` at the places `0, 1, 1/2, …, 1/(s-1)` and `v = (1, 1, 2, …, s-1)`
is a digital `(0,s)`-sequence, at every full level `P_{s²K}` the geometric digits follow the design exactly, and
`sep(P_{s²K}) ≥ 1 - (a*_s+1)/p` for every `K ≥ 1`. -/
theorem blkS_block {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hp : 5 * Z3NetA.aStar s + 4 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blkS s θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (s * K)) →
        seqDigit (zcode p) (blkS s θ) x i (s * K) =
          ∑ c, ∑ n ∈ range (s - 1), ustarFd s n i c * seqDigit (zcode p) (blkS s θ) x c (s * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p s (s * K) (seqPoint (zcode p) (blkS s θ))
        (((p : ℝ) - Z3NetA.aStar s - 1) / p) := by
  have hsp : s ≤ p := by have := aStar_ge hs; omega
  have ha := ustarA_injective (p := p) hsp
  have hv := ustarV_ne (p := p) hsp
  have hv1 : ∀ c, (1 : Fin s → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := ustar_hNd (p := p) hs hsp
  have hrel := ustar_hrel (p := p) hs hsp
  refine ⟨blockGen_t0 θ s (ustarV s) _ (ustarNd s) 1 (zcode p) ha hθ le_rfl (by omega) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq (ustarA s) θ s (ustarV s) _ (ustarNd s) 1 (zcode p) ha hθ le_rfl
      (by omega) hrel hv K hK i x hx, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - Z3NetA.aStar s - 1) / p ≤ 1 := by
    rw [div_le_one hp0]; have : (0 : ℝ) ≤ Z3NetA.aStar s := Nat.cast_nonneg _; linarith
  have h := block_sep (ustarA s) ha θ hθ s le_rfl (by omega) (ustarV s) hv (ustarFd s) (ustarNd s) 1 hv1 hNd hrel
    K hK _ (ustar_LB_proof hs hp (s * K))
  rwa [min_eq_right hLB1] at h

/-! ## Equality: the column of the place `0` -/

/-- The column of the place `∞` of the nets (coordinate `0`, the place `0` here) at level `0` is `(0, 1, …, 1)`:
`E_{∞,0}` is the positive generator of `Λ_0 = ℤ (0, 1, …, 1)`. -/
theorem ustar_col0 {s : ℕ} [NeZero s] (hs : 3 ≤ s) (c : Fin s) (hc : c ≠ 0) : Z3NetA.UstarF s 0 c 0 = 1 := by
  classical
  set V : Fin s → ℤ := fun c => if c = 0 then 0 else 1 with hV
  have hw : ∀ c : Fin s, Z3NetA.wQ c 0 = 1 := fun c => by simp [Z3NetA.wQ, Z3NetF.wN]
  have hrep : ∀ c, c ≠ 0 → (V c : ℚ) = Z3NetA.wQ c 0 * (C (1 : ℚ)).eval (Z3NetA.yQ c 0) := by
    intro c hc; simp [hV, hc, hw]
  have hVl : Z3NetA.InLam (0 : Fin s) 0 V := ⟨by simp [hV], C 1, by simp, hrep⟩
  have hVk : Z3NetA.kappa (0 : Fin s) 0 V = 1 := by
    rw [Z3NetA.Proofs.kappa_eq hs (by omega) V (C 1) (by simp) hrep, coeff_C_zero]
  have hgam : Z3NetA.gamS (0 : Fin s) 0 = 1 := by
    obtain ⟨hpos, hspec⟩ := Z3NetA.Proofs.gamS_spec hs (0 : Fin s) 0 (by omega)
    obtain ⟨z, hz⟩ := (hspec 1).1 ⟨V, hVl, hVk⟩
    obtain ⟨E, hE, hEk⟩ := (hspec (Z3NetA.gamS (0 : Fin s) 0)).2 ⟨1, by rw [Int.cast_one, one_mul]⟩
    obtain ⟨-, g, hg, hrepE⟩ := hE
    have hk := Z3NetA.Proofs.kappa_eq hs (by omega) E g hg hrepE
    have h1 : (1 : Fin s) ≠ 0 := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have hE1 := hrepE 1 h1
    rw [hw, one_mul, eq_C_of_natDegree_le_zero hg, eval_C] at hE1
    rw [hk] at hEk
    -- `γ = E_1 ∈ ℤ`, `γ > 0`, `z γ = 1`
    have hγ : Z3NetA.gamS (0 : Fin s) 0 = (E 1 : ℚ) := by rw [← hEk, hE1]
    rw [hγ] at hz hpos
    have hzE : z * E 1 = 1 := by exact_mod_cast hz.symm
    have hE1pos : 0 < E 1 := by exact_mod_cast hpos
    have : E 1 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hzE with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · omega
    rw [hγ, this, Int.cast_one]
  have hE := (Z3NetA.Proofs.isUstarCols_iff (0 : Fin s) _).1 (Z3NetA.Ustar_cols hs (0 : Fin s))
  have hBel : Z3NetA.Proofs.Below (0 : Fin s) (Z3NetA.Ecol 0) 0 := fun i hi => absurd hi (by omega)
  have hcol : Z3NetA.Ecol (0 : Fin s) 0 = V :=
    Z3NetA.Proofs.level_unique hs (0 : Fin s) (Z3NetA.Ecol 0) 0 (by omega) hBel _ _ (hE.1 0 (by omega))
      ⟨hVl, by rw [hVk, hgam], fun _ => 0, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
  have hs1 : ¬ s - 1 ≤ 0 := by omega
  have : Z3NetA.UstarF s 0 c 0 = Z3NetA.Ecol 0 0 c := by simp [Z3NetA.UstarF, hc, hs1]
  rw [this, hcol]
  simp [hV, hc]

/-- **Upper bound in `thm:block`(c)**, every prime `p > a*_s + 1`: the axis step along the coordinate of the place `0`
(carry length `1`) has the term `1 - (α_0 + 1)/p`. -/
theorem blkS_axis {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hp : Z3NetA.alphaS (0 : Fin s) < p) (K : ℕ) (hK : 1 ≤ K) :
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2) =
      ((p : ℝ) - Z3NetA.alphaS (0 : Fin s) - 1) / p := by
  obtain ⟨h1, h2⟩ := axis_term (p := p) (by omega) (Z3NetA.UstarF s) (Z3NetF.Msum (Z3NetA.UstarF s))
    (fun j _ i c => rfl) (0 : Fin s) (Z3NetA.alphaS 0)
    (by simp [Z3NetF.Msum, (Z3NetA.Ustar_dominant hs 0).1]) hp
    (fun i hi => by simp [Z3NetF.Msum, ustar_col0 hs i hi]) K hK
  exact ⟨_, _, h1, h2⟩

/-- **Equality in `thm:block`(c) for every `s ≥ 3`, conditional form**: if the row of the place `0` has the largest
`α` (`α_0 = a*_s`; the paper checks this by exact computation for `s ≤ 10`), then `LB(F) = 1 - (a*_s+1)/p` for every
prime `p ≥ 5 a*_s + 4`: every step has a term `≥ 1 - (a*_s+1)/p`, and the axis step at the place `0` attains it. -/
theorem blkS_LB_eq_of {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hmax : Z3NetA.alphaS (0 : Fin s) = Z3NetA.aStar s)
    (hp : 5 * Z3NetA.aStar s + 4 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - Z3NetA.aStar s - 1) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (s - 1)), ustarFd s n i c') : ℝ) / p) ^ 2) =
      ((p : ℝ) - Z3NetA.aStar s - 1) / p := by
  refine ⟨ustar_LB_proof hs hp K, ?_⟩
  rw [← hmax]
  exact blkS_axis hs (by omega) K hK

/-! ## The free diagonal, every `s` -/

lemma ustarDiag_off {s : ℕ} [NeZero s] (δ : Fin s → ℤ) {i c : Fin s} (h : i ≠ c) (n : ℕ) :
    blockF (F := ZMod p) (ustarDiagF s δ) n i c = ustarFd s n i c := by
  simp [blockF, ustarDiagF, ustarFd, h]

/-- Identity (a) for the design with the free diagonal (it does not involve the diagonal). -/
theorem ustarDiag_hrel {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (δ : Fin s → ℤ) (c i : Fin s) (h : i ≠ c) :
    wCoCo (ustarA (p := p) s) c i = -C (ustarV s i) *
      ∑ n ∈ range (s - 1), C (blockF (ustarDiagF s δ) n i c) * ustarNd s c (s - 1 - n) := by
  rw [ustar_hrel hs hsp c i h]
  have hsum : ∑ n ∈ range (s - 1), C (ustarFd (p := p) s n i c) * ustarNd s c (s - 1 - n) =
      ∑ n ∈ range (s - 1), C (blockF (F := ZMod p) (ustarDiagF s δ) n i c) * ustarNd s c (s - 1 - n) :=
    Finset.sum_congr rfl (fun (n : ℕ) (_ : n ∈ range (s - 1)) => by rw [ustarDiag_off δ h])
  rw [hsum]

/-- **The free diagonal, every `s ≥ 3`**: for every diagonal `δ` (`F_0[c][c] = -δ_c`, the off-diagonal entries of
`U*_s`), every prime `p ≥ s` and `θ ≠ 0`, `blkSd s δ θ` is a digital `(0,s)`-sequence, the geometric digits follow the
design at every `P_{s²K}`, and `sep(P_{s²K}) ≥ min(1, LB)` for every lower bound `LB` of the one-digit relaxation. -/
theorem blkSd_block {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (δ : Fin s → ℤ) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blkSd s δ θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (s * K)) →
        seqDigit (zcode p) (blkSd s δ θ) x i (s * K) =
          ∑ c, ∑ n ∈ range (s - 1), blockF (ustarDiagF s δ) n i c *
            seqDigit (zcode p) (blkSd s δ θ) x c (s * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → ∀ LB : ℝ, (∀ e l, IsStep (s * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
        (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF (ustarDiagF s δ) n i c') : ℝ) / p) ^ 2)) →
        SepAtLevel p s (s * K) (seqPoint (zcode p) (blkSd s δ θ)) (min 1 LB) := by
  have ha := ustarA_injective (p := p) hsp
  have hv := ustarV_ne (p := p) hsp
  have hv1 : ∀ c, (1 : Fin s → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := ustar_hNd (p := p) hs hsp
  have hrel := ustarDiag_hrel (p := p) hs hsp δ
  exact ⟨blockGen_t0 θ s (ustarV s) _ (ustarNd s) 1 (zcode p) ha hθ le_rfl (by omega) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq (ustarA s) θ s (ustarV s) _ (ustarNd s) 1 (zcode p) ha hθ le_rfl
      (by omega) hrel hv K hK i x hx,
    fun K hK LB hLB => block_sep (ustarA s) ha θ hθ s le_rfl (by omega) (ustarV s) hv _ (ustarNd s) 1 hv1 hNd hrel
      K hK LB hLB⟩

/-- **The free diagonal with the sign-class condition, every `s ≥ 3`**: if every step of the design `ustarDiagF s δ`
has a backward coordinate with `|σ| ≤ A` or two backward coordinates (`SignClass`, independent of `p`), then
`sep(P_{s²K}) ≥ 1 - (A+1)/p` for every prime `p ≥ s` past the threshold of `sc_LB` (`S` a bound for the row sums of
`max_j |M^{(j)}|`, `S < p`, `(p - A - 1)² ≤ 2 (p - S - 1)²`). -/
theorem blkSd_block_sc {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) (δ : Fin s → ℤ) (A S : ℕ)
    (Bd : Fin s → Fin s → ℤ)
    (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Z3NetF.Msum (ustarDiagF s δ) j i c| ≤ Bd i c) (hS : ∀ i, ∑ c, Bd i c ≤ S)
    (hSp : S < p) (hAS : A ≤ S) (hq : ((p : ℤ) - A - 1) ^ 2 ≤ 2 * ((p : ℤ) - S - 1) ^ 2)
    (hcl : SignClass (Z3NetF.Msum (ustarDiagF s δ)) A) (θ : ZMod p) (hθ : θ ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p s (s * K) (seqPoint (zcode p) (blkSd s δ θ)) (((p : ℝ) - A - 1) / p) := by
  have h := (blkSd_block hs hsp δ θ hθ).2.2 K hK _
    (sc_LB (by omega) (ustarDiagF s δ) (Z3NetF.Msum (ustarDiagF s δ)) (fun j _ i c => rfl) Bd hB S A hS hSp hAS hq
      hcl (s * K))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - A - 1) / p ≤ 1 := by
    rw [div_le_one hp0]; have : (0 : ℝ) ≤ A := Nat.cast_nonneg _; linarith
  rwa [min_eq_right hLB1] at h

/-! ## Every reachable integer design -/

/-- **`thm:block`(i)–(iii) for every reachable design** (with the numerators `designNd` of `def:block`(a)): for
distinct places, nonzero row constants, an integer design reachable modulo `p`, and `θ ≠ 0`, the block-periodic residue
sequence with `ℓ = s` is a digital `(0,s)`-sequence, follows the design at every `P_{s²K}`, and has
`sep(P_{s²K}) ≥ min(1, LB)` for every lower bound `LB` of the one-digit relaxation. -/
theorem reach_block {s : ℕ} (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (v : Fin s → ZMod p)
    (hv : ∀ c, v c ≠ 0) (Fz : ℕ → Fin s → Fin s → ℤ) (γ : Fin s → ℕ → (ZMod p)[X])
    (hR : IsReachable a v (blockF Fz) γ) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (s * K)) →
        seqDigit (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1) x i (s * K) =
          ∑ c, ∑ n ∈ range (s - 1), blockF Fz n i c *
            seqDigit (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1) x c (s * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → ∀ LB : ℝ, (∀ e l, IsStep (s * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
        (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2)) →
        SepAtLevel p s (s * K) (seqPoint (zcode p) (blockGen a θ s v (blockF Fz) (designNd a v (blockF Fz)) 1))
          (min 1 LB) := by
  obtain ⟨hrel, hNd⟩ := designNd_spec hs a ha v hv _ γ hR
  have hv1 : ∀ c, (1 : Fin s → ZMod p) c ≠ 0 := fun c => one_ne_zero
  exact ⟨blockGen_t0 θ s v _ _ 1 (zcode p) ha hθ le_rfl (by omega) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq a θ s v _ _ 1 (zcode p) ha hθ le_rfl (by omega) hrel hv K hK i x hx,
    fun K hK LB hLB => block_sep a ha θ hθ s le_rfl hs v hv _ _ 1 hv1 hNd hrel K hK LB hLB⟩

end GeoSeq
