/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Res
public import GeoSeq.V9Kor

@[expose] public section

/-!
# GeoSeq stage V9-6 (part 2): certificates for block-periodic sequences and skeleton relations

* `blockGen_carry` (`thm:block`(iii)): at every design level `ℓK` the one-digit carry responses are
  `D(l) = M^{(min(l, s-1) - 1)} = ∑_{n < min(l, s-1)} F_n`, independent of `K`.
* **`block_sep`** (`thm:block`(iii), `thm:blocktwo`(ii)): `sep(P_{sℓK}) ≥ min(1, LB)` for every `LB` below the one-digit
  relaxation of `lem:cert` with these responses.
* **`skel_sep`**, `skel_sepAtPrefix` (the proof of `thm:residue`(ii) for any digital `(0,s)`-sequence over `ℤ/pℤ`): a
  skeleton relation `∑_c v_c y_{c,K-1} = 0` on `P_{sK-1}` gives `sep(P_{sK-1}) ≥ p^{-1/s} L` for every `L` below
  `‖(|b| - 𝟏)_+‖_2` on `Λ_v \ {0}`; `skel_cells` (the occupied fine cells lie in `Λ_v`).
-/

namespace GeoSeq

open Finset Polynomial

section Carry
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F) (ℓ : ℕ) (v : Fin s → F) (Fd : ℕ → Fin s → Fin s → F)
  (Nd : Fin s → ℕ → F[X]) (v' : Fin s → F)

/-- **The carry responses of a block-periodic sequence** at the design level `ℓK` (`thm:block`(iii)): adding `1` to the
`l` finest cell digits of coordinate `c'` changes the geometric digit of coordinate `i` by
`∑_{n < min(l, s-1)} F_n[i][c']`. -/
theorem blockGen_carry {q : ℕ} [NeZero q] (D : DigitCode F q) (ha : Function.Injective a) (hθ : θ ≠ 0)
    (hsℓ : s ≤ ℓ) (hs : 1 ≤ s)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hnet : BlockNet0 D (blockGen a θ ℓ v Fd Nd v') (s * (ℓ * K)) 0) (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ ℓ * K)
    (i c' : Fin s) :
    IsCarryEntry (blockGen a θ ℓ v Fd Nd v') (ℓ * K) 0 l i c' (∑ n ∈ range (min l (s - 1)), Fd n i c') := by
  obtain ⟨d, hd⟩ := carry_exists D (blockGen a θ ℓ v Fd Nd v') (ℓ * K) hnet 0 l i c'
  suffices h : d = ∑ n ∈ range (min l (s - 1)), Fd n i c' by rw [← h]; exact hd
  obtain ⟨V, hV⟩ := hd.1
  rw [← hd.2 V hV, add_zero]
  set f : ℕ → F := fun j => if h : j < s * (ℓ * K) then V ⟨j, h⟩ else 0 with hf
  have hvd : ∀ c n, vecDigit (blockGen a θ ℓ v Fd Nd v') V c n =
      blockDig a θ ℓ v Fd Nd v' c n (vecPoly f (s * (ℓ * K))) := by
    intro c n
    rw [← blockGen_vecPoly, vecDigit, ← Fin.sum_univ_eq_sum_range (fun j => blockGen a θ ℓ v Fd Nd v' c n j * f j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hf, j.isLt]
  rw [hvd, blockGen_rel a θ ℓ v Fd Nd v' ha hθ hsℓ hs hrel hv K hK i f _ le_rfl]
  simp_rw [← hvd]
  have hℓK : s - 1 ≤ ℓ * K := le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega) : ℓ ≤ ℓ * K)
  have hterm : ∀ c, ∑ n ∈ range (s - 1), Fd n i c * vecDigit (blockGen a θ ℓ v Fd Nd v') V c (ℓ * K - 1 - n) =
      if c = c' then ∑ n ∈ range (min l (s - 1)), Fd n i c' else 0 := by
    intro c
    have : ∀ n ∈ range (s - 1), Fd n i c * vecDigit (blockGen a θ ℓ v Fd Nd v') V c (ℓ * K - 1 - n) =
        if c = c' ∧ n < l then Fd n i c' else 0 := by
      intro n hn
      have hn' := Finset.mem_range.mp hn
      rw [hV c (ℓ * K - 1 - n) (by omega), carryPat]
      by_cases hc : c = c'
      · subst hc
        by_cases hnl : n < l
        · rw [if_pos ⟨rfl, by omega, by omega⟩, if_pos ⟨rfl, hnl⟩, mul_one]
        · rw [if_neg (fun h => hnl (by omega)), if_neg (fun h => hnl h.2), mul_zero]
      · rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1), mul_zero]
    rw [Finset.sum_congr rfl this]
    by_cases hc : c = c'
    · subst hc
      simp only [true_and, if_true]
      rw [← Finset.sum_filter, show (range (s - 1)).filter (fun n => n < l) = range (min l (s - 1)) by
        ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega]
    · simp [hc]
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_ite_eq']
  simp

end Carry

section Sep
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`thm:block`(iii)**, **`thm:blocktwo`(ii)** (over `ℤ/pℤ`): with the responses `D(l) = ∑_{n < min(l,s-1)} F_n`,
`sep(P_{sℓK}) ≥ min(1, LB)` for every `K ≥ 1` and every `LB` at most the one-digit relaxation of `lem:cert`. -/
theorem block_sep (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (K : ℕ) (hK : 1 ≤ K) (LB : ℝ)
    (hLB : ∀ e l, IsStep (ℓ * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2)) :
    SepAtLevel p s (ℓ * K) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v')) (min 1 LB) := by
  have hs : 1 ≤ s := by omega
  have hnet := blockGen_t0 θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hv hv' hNd (s * (ℓ * K)) 0
  have hq : 4 ≤ p ^ (ℓ * K) := le_trans (by
    have := (Fact.out : p.Prime).two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left this 2) (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by
        have : ℓ ≤ ℓ * K := Nat.le_mul_of_pos_right _ (by omega)
        omega))
  exact cert_one _ (ℓ * K) hq hnet (fun l i c' => ∑ n ∈ range (min l (s - 1)), Fd n i c')
    (fun l hl hlK i c' => blockGen_carry a θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hrel hv K hK hnet l hl hlK i c')
    LB hLB

/-- The fine cells of a sequence with a skeleton relation lie in `Λ_v` (`thm:residue`(i), first half, for any
digital sequence over `ℤ/pℤ`). -/
theorem skel_cells (C : Gen s (ZMod p)) (v : Fin s → ZMod p) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) (x : ℕ)
    (hx : x < p ^ (s * K - 1)) : InLat v (fun c => (cellIdx (zcode p) C x c K : ℤ)) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have := hskel x hx
  unfold InLat
  simp only [Int.cast_natCast, cast_cellIdx]
  simpa using this

lemma skel_inj (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (K : ℕ) (hK : 1 ≤ K)
    (x y : ℕ) (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1))
    (h : ∀ c, cellIdx (zcode p) C x c K = cellIdx (zcode p) C y c K) : x = y := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set c0 : Fin s := ⟨0, by omega⟩
  obtain ⟨z, -, hz⟩ := hseq (s * (K' + 1) - 1) 0 (skelDepth c0 (K' + 1))
    (skelDepth_sum c0 _ hK) (fun c => cellIdx (zcode p) C x c (skelDepth c0 (K' + 1) c))
    (fun c => cellIdx_lt _ _ _ _ _)
  have hcell : ∀ w, (∀ c, cellIdx (zcode p) C w c (K' + 1) = cellIdx (zcode p) C x c (K' + 1)) →
      ∀ c, cellIdx (zcode p) C w c (skelDepth c0 (K' + 1) c) =
        cellIdx (zcode p) C x c (skelDepth c0 (K' + 1) c) := by
    intro w hw c
    unfold skelDepth
    split_ifs
    · simp only [Nat.add_sub_cancel]
      rw [← cellIdx_div (zcode p) C w c K', ← cellIdx_div (zcode p) C x c K', hw c]
    · exact hw c
  have hxz := hz x ⟨by simp [hx], fun c => rfl⟩
  have hyz := hz y ⟨by simp [hy], hcell y fun c => (h c).symm⟩
  rw [hxz, hyz]

/-- **The skeleton bound** (the proof of `thm:residue`(ii) for any digital `(0,s)`-sequence over `ℤ/pℤ`): if
`∑_c v_c y_{c,K-1}(x) = 0` for every `x < p^{sK-1}` and `L ≤ ‖(|b| - 𝟏)_+‖_2` for every `0 ≠ b ∈ Λ_v`, then any two
distinct points of `P_{sK-1}` are at toroidal distance `≥ L p^{-K}`. -/
theorem skel_sep (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (v : Fin s → ZMod p)
    (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    L ≤ (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
  set Q : ℕ := p ^ K with hQdef
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hQ : 0 < Q := pow_pos hp K
  set n : Fin s → ℕ := fun c => cellIdx (zcode p) C x c K
  set m : Fin s → ℕ := fun c => cellIdx (zcode p) C y c K
  set b : Fin s → ℤ := fun c => cenRep Q ((m c : ℤ) - n c)
  have hn : ∀ c, n c < Q := fun c => cellIdx_lt _ _ _ _ _
  have hm : ∀ c, m c < Q := fun c => cellIdx_lt _ _ _ _ _
  have hD : ∀ c, |((m c : ℤ) - n c)| < Q := fun c => by
    have := hn c; have := hm c; rw [abs_lt]; omega
  have hb0 : b ≠ 0 := by
    intro hb
    apply hxy
    refine skel_inj hs C hseq K hK x y hx hy fun c => ?_
    have := cenRep_eq_zero Q _ (hD c) (congrFun hb c)
    show n c = m c
    omega
  have hblat : InLat v b := by
    have hx' : InLat v (fun c => ((n c : ℕ) : ℤ)) := skel_cells C v K hK hskel x hx
    have hy' : InLat v (fun c => ((m c : ℕ) : ℤ)) := skel_cells C v K hK hskel y hy
    unfold InLat at hx' hy' ⊢
    have hcast : ∀ c, ((b c : ℤ) : ZMod p) = ((m c : ℤ) : ZMod p) - ((n c : ℤ) : ZMod p) := by
      intro c
      obtain ⟨t, ht⟩ := cenRep_modEq Q ((m c : ℤ) - n c)
      show ((cenRep Q ((m c : ℤ) - n c) : ℤ) : ZMod p) = _
      rw [ht]
      push_cast
      rw [hQdef]
      push_cast
      rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
    calc ∑ c, v c * ((b c : ℤ) : ZMod p)
        = ∑ c, (v c * (((m c : ℕ) : ℤ) : ZMod p) - v c * (((n c : ℕ) : ℤ) : ZMod p)) :=
          Finset.sum_congr rfl fun c _ => by rw [hcast c, mul_sub]
      _ = 0 := by
          beta_reduce at hx' hy'
          exact (Finset.sum_sub_distrib _ _).trans ((congrArg₂ (· - ·) hy' hx').trans (sub_zero 0))
  have hLb := hL b hb0 hblat
  have hcoord : ∀ c, max (|((b c : ℤ) : ℝ)| - 1) 0 ≤
      (Q : ℝ) * Z3NetDGS.torCoord (seqPoint (zcode p) C x c) (seqPoint (zcode p) C y c) :=
    fun c => torCoord_cell Q hQ _ _ (n c) (m c) (hn c) (hm c) (seqPoint_cell C x c K)
      (seqPoint_cell C y c K) (seqPoint_unit C x c) (seqPoint_unit C y c)
  have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  calc L ≤ jitNorm b := hLb
    _ ≤ Real.sqrt (∑ c, ((Q : ℝ) *
          Z3NetDGS.torCoord (seqPoint (zcode p) C x c) (seqPoint (zcode p) C y c)) ^ 2) := by
        unfold jitNorm
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
        exact pow_le_pow_left₀ (le_max_right _ _) (hcoord c) 2
    _ = (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
        unfold Z3NetDGS.torDist2
        simp_rw [mul_pow]
        rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq hQr, hQdef]
        push_cast
        rfl

/-- `skel_sep` in the paper's normalization: `sep(P_{sK-1}) ≥ p^{-1/s} L`. -/
theorem skel_sepAtPrefix (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (v : Fin s → ZMod p)
    (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) C) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  intro x y hx hy hxy
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := skel_sep hs C hseq v L hL K hK hskel x y hx hy hxy
  have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  calc (p : ℝ) ^ (-(1 / (s : ℝ))) * L * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))
      = L * ((p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))) := by ring
    _ = L / (p : ℝ) ^ K := by rw [prefix_scale hp (by omega) K hK, div_eq_mul_inv]
    _ ≤ _ := by rw [div_le_iff₀ hpK]; linarith

end Sep

end GeoSeq
