/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V97Sep
public import GeoSeq.V7Shift

@[expose] public section

/-!
# GeoSeq stage V9-7 (part 3): digital shifts of residue sequences (`lem:shift`(b))

* `shCell_succ`, `shCell_div`, `cast_shCell`: the shifted fine-cell index.
* `skel_inj_sh`: distinct points of the shifted prefix `P_{sK-1}` lie in distinct fine cells.
* `shift_skel_rel`: a skeleton relation `∑_c v_c y_{c,K-1} = 0` becomes `∑_c v_c n̂_c ≡ ∑_c v_c ς_{c,K-1}` for the shifted
  fine cells.
* **`shift_skel_sep`**, **`shift_residue`** (**`lem:shift`(b)**): the occupied fine cells of the shifted prefix `P_{sK-1}`
  of a residue sequence are exactly the cells of `[0, p^K)^s` with `∑_c v_c n̂_c ≡ ∑_c v_c ς_{c,K-1}`, each holding one
  point, and `sep(P_{sK-1}) ≥ p^{-1/s} ℓ_jit(Λ_v)` for the shifted sequence.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

lemma shCell_succ (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (x : ℕ) (c : Fin s) (K : ℕ) :
    shCell (zcode p) C ς x c (K + 1) = shCell (zcode p) C ς x c K * p +
      ((zcode p).enc (shDigit (zcode p) C ς x c K) : ℕ) := by
  unfold shCell
  rw [Fin.sum_univ_castSucc, Finset.sum_mul]
  simp only [Fin.coe_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn := n.isLt
  rw [mul_assoc, ← pow_succ]
  congr 2
  omega

lemma shCell_lt (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (x : ℕ) (c : Fin s) (K : ℕ) :
    shCell (zcode p) C ς x c K < p ^ K :=
  Z3Net.Proofs.digSum_lt p K _ (fun _ => ((zcode p).enc _).isLt)

lemma shCell_div (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (x : ℕ) (c : Fin s) (K : ℕ) :
    shCell (zcode p) C ς x c (K + 1) / p = shCell (zcode p) C ς x c K := by
  rw [shCell_succ, mul_comm, Nat.mul_add_div (Fact.out : p.Prime).pos,
    Nat.div_eq_of_lt ((zcode p).enc (shDigit (zcode p) C ς x c K)).isLt, add_zero]

lemma cast_shCell (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (x : ℕ) (c : Fin s) (K : ℕ) :
    ((shCell (zcode p) C ς x c (K + 1) : ℕ) : ZMod p) = shDigit (zcode p) C ς x c K := by
  rw [shCell_succ]
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_add]
  exact ZMod.natCast_zmod_val _

lemma skel_inj_sh (hs : 2 ≤ s) (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (hsh : IsSeq0Sh (zcode p) C ς)
    (K : ℕ) (hK : 1 ≤ K) (x y : ℕ) (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1))
    (h : ∀ c, shCell (zcode p) C ς x c K = shCell (zcode p) C ς y c K) : x = y := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set c0 : Fin s := ⟨0, by omega⟩
  obtain ⟨z, -, hz⟩ := hsh (s * (K' + 1) - 1) 0 (skelDepth c0 (K' + 1))
    (skelDepth_sum c0 _ hK) (fun c => shCell (zcode p) C ς x c (skelDepth c0 (K' + 1) c))
    (fun c => shCell_lt _ _ _ _ _)
  have hcell : ∀ w, (∀ c, shCell (zcode p) C ς w c (K' + 1) = shCell (zcode p) C ς x c (K' + 1)) →
      ∀ c, shCell (zcode p) C ς w c (skelDepth c0 (K' + 1) c) =
        shCell (zcode p) C ς x c (skelDepth c0 (K' + 1) c) := by
    intro w hw c
    unfold skelDepth
    split_ifs
    · simp only [Nat.add_sub_cancel]
      rw [← shCell_div C ς w c K', ← shCell_div C ς x c K', hw c]
    · exact hw c
  have hxz := hz x ⟨by simp [hx], fun c => rfl⟩
  have hyz := hz y ⟨by simp [hy], hcell y fun c => (h c).symm⟩
  rw [hxz, hyz]

/-- A skeleton relation for the unshifted digits gives the affine relation `∑_c v_c n̂_c ≡ ∑_c v_c ς_{c,K-1}` for the
shifted fine cells. -/
theorem shift_skel_rel (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (v : Fin s → ZMod p) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) (x : ℕ)
    (hx : x < p ^ (s * K - 1)) :
    ∑ c, v c * ((shCell (zcode p) C ς x c K : ℕ) : ZMod p) = ∑ c, v c * ς c (K - 1) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [cast_shCell, shDigit, mul_add, Finset.sum_add_distrib, Nat.add_sub_cancel]
  rw [show ∑ c, v c * seqDigit (zcode p) C x c K' = 0 by simpa using hskel x hx, zero_add]

lemma sum_mul_sub_const {ι R : Type*} [CommRing R] (t : Finset ι) (v Y X : ι → R) (κ : R)
    (hY : ∑ i ∈ t, v i * Y i = κ) (hX : ∑ i ∈ t, v i * X i = κ) : ∑ i ∈ t, v i * (Y i - X i) = 0 := by
  simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, hY, hX, sub_self]

lemma shPoint_unit (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (x : ℕ) (c : Fin s) :
    0 ≤ shPoint (zcode p) C ς x c ∧ shPoint (zcode p) C ς x c ≤ 1 := by
  have := shift_coord_cell (Fact.out : p.Prime).two_le (zcode p) C ς x c 0
  simp only [pow_zero, one_mul] at this
  have h0 : shCell (zcode p) C ς x c 0 = 0 := by simp [shCell]
  rw [h0] at this
  simpa using this

/-- **The skeleton bound for shifted sequences** (`lem:shift`(b), separation): if `C` is a digital `(0,s)`-sequence over
`ℤ/pℤ` with the skeleton relation on `P_{sK-1}`, then every digitally shifted copy has `sep(P_{sK-1}) ≥ p^{-1/s} L` for
every `L ≤ ‖(|b| - 𝟏)_+‖_2` on `Λ_v \ {0}`. -/
theorem shift_skel_sep (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (ς : Fin s → ℕ → ZMod p)
    (v : Fin s → ZMod p) (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) :
    SepAtPrefix p s (s * K - 1) (shPoint (zcode p) C ς) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  have hsh := (shift_seq0 (zcode p) C ς).mpr hseq
  have hmain : ∀ x y, x < p ^ (s * K - 1) → y < p ^ (s * K - 1) → x ≠ y →
      L ≤ (p : ℝ) ^ K * Z3NetDGS.torDist2 (shPoint (zcode p) C ς x) (shPoint (zcode p) C ς y) := by
    intro x y hx hy hxy
    set Q : ℕ := p ^ K with hQdef
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hQ : 0 < Q := pow_pos hp K
    set n : Fin s → ℕ := fun c => shCell (zcode p) C ς x c K
    set m : Fin s → ℕ := fun c => shCell (zcode p) C ς y c K
    set b : Fin s → ℤ := fun c => cenRep Q ((m c : ℤ) - n c)
    have hn : ∀ c, n c < Q := fun c => shCell_lt _ _ _ _ _
    have hm : ∀ c, m c < Q := fun c => shCell_lt _ _ _ _ _
    have hD : ∀ c, |((m c : ℤ) - n c)| < Q := fun c => by
      have := hn c; have := hm c; rw [abs_lt]; omega
    have hb0 : b ≠ 0 := by
      intro hb
      apply hxy
      refine skel_inj_sh hs C ς hsh K hK x y hx hy fun c => ?_
      have := cenRep_eq_zero Q _ (hD c) (congrFun hb c)
      show n c = m c
      omega
    have hblat : InLat v b := by
      have hx' := shift_skel_rel C ς v K hK hskel x hx
      have hy' := shift_skel_rel C ς v K hK hskel y hy
      unfold InLat
      have hcast : ∀ c, ((b c : ℤ) : ZMod p) = ((m c : ℕ) : ZMod p) - ((n c : ℕ) : ZMod p) := by
        intro c
        obtain ⟨t, ht⟩ := cenRep_modEq Q ((m c : ℤ) - n c)
        show ((cenRep Q ((m c : ℤ) - n c) : ℤ) : ZMod p) = _
        rw [ht]
        push_cast
        rw [hQdef]
        push_cast
        rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
      rw [Finset.sum_congr rfl fun c _ => by rw [hcast c]]
      exact sum_mul_sub_const univ v _ _ _ hy' hx'
    have hLb := hL b hb0 hblat
    have hcoord : ∀ c, max (|((b c : ℤ) : ℝ)| - 1) 0 ≤
        (Q : ℝ) * Z3NetDGS.torCoord (shPoint (zcode p) C ς x c) (shPoint (zcode p) C ς y c) := by
      intro c
      have h1 := shift_coord_cell (Fact.out : p.Prime).two_le (zcode p) C ς x c K
      have h2 := shift_coord_cell (Fact.out : p.Prime).two_le (zcode p) C ς y c K
      have h1' : ((n c : ℕ) : ℝ) ≤ (Q : ℝ) * shPoint (zcode p) C ς x c ∧
          (Q : ℝ) * shPoint (zcode p) C ς x c ≤ (n c : ℝ) + 1 := by rw [hQdef, Nat.cast_pow]; exact h1
      have h2' : ((m c : ℕ) : ℝ) ≤ (Q : ℝ) * shPoint (zcode p) C ς y c ∧
          (Q : ℝ) * shPoint (zcode p) C ς y c ≤ (m c : ℝ) + 1 := by rw [hQdef, Nat.cast_pow]; exact h2
      exact torCoord_cell Q hQ _ _ (n c) (m c) (hn c) (hm c) h1' h2' (shPoint_unit C ς x c)
        (shPoint_unit C ς y c)
    have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    calc L ≤ jitNorm b := hLb
      _ ≤ Real.sqrt (∑ c, ((Q : ℝ) *
            Z3NetDGS.torCoord (shPoint (zcode p) C ς x c) (shPoint (zcode p) C ς y c)) ^ 2) := by
          unfold jitNorm
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
          exact pow_le_pow_left₀ (le_max_right _ _) (hcoord c) 2
      _ = (p : ℝ) ^ K * Z3NetDGS.torDist2 (shPoint (zcode p) C ς x) (shPoint (zcode p) C ς y) := by
          unfold Z3NetDGS.torDist2
          simp_rw [mul_pow]
          rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq hQr, hQdef]
          push_cast
          rfl
  intro x y hx hy hxy
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := hmain x y hx hy hxy
  have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  calc (p : ℝ) ^ (-(1 / (s : ℝ))) * L * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))
      = L * ((p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))) := by ring
    _ = L / (p : ℝ) ^ K := by rw [prefix_scale hp (by omega) K hK, div_eq_mul_inv]
    _ ≤ _ := by rw [div_le_iff₀ hpK]; linarith


lemma skel_surj_sh (hs : 2 ≤ s) (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (hsh : IsSeq0Sh (zcode p) C ς)
    (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0)
    (n : Fin s → ℕ) (hn : ∀ c, n c < p ^ K)
    (hrel : ∑ c, v c * ((n c : ℕ) : ZMod p) = ∑ c, v c * ς c (K - 1)) :
    ∃ x, x < p ^ (s * K - 1) ∧ ∀ c, shCell (zcode p) C ς x c K = n c := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set c0 : Fin s := ⟨0, by omega⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set tgt : Fin s → ℕ := fun c => if c = c0 then n c0 / p else n c
  obtain ⟨x, ⟨⟨-, hxlt⟩, hx⟩, -⟩ := hsh (s * (K' + 1) - 1) 0 (skelDepth c0 (K' + 1))
    (skelDepth_sum c0 _ hK) tgt (by
      intro c
      simp only [tgt, skelDepth]
      split_ifs with hc
      · simp only [Nat.add_sub_cancel]
        rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]; exact hn c0
      · exact hn c)
  rw [zero_add, one_mul] at hxlt
  refine ⟨x, hxlt, ?_⟩
  have hoth : ∀ c, c ≠ c0 → shCell (zcode p) C ς x c (K' + 1) = n c := by
    intro c hc
    have := hx c
    simp only [skelDepth, tgt, if_neg hc] at this
    exact this
  have hdiv : shCell (zcode p) C ς x c0 (K' + 1) / p = n c0 / p := by
    have := hx c0
    simp only [skelDepth, tgt, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [shCell_div C ς x c0 K']
    exact this
  have hxl := shift_skel_rel C ς v (K' + 1) hK hskel x hxlt
  rw [← hrel, ← Finset.add_sum_erase _ _ (mem_univ c0), ← Finset.add_sum_erase _ _ (mem_univ c0)] at hxl
  have hrest : ∑ c ∈ univ.erase c0, v c * ((shCell (zcode p) C ς x c (K' + 1) : ℕ) : ZMod p) =
      ∑ c ∈ univ.erase c0, v c * ((n c : ℕ) : ZMod p) :=
    Finset.sum_congr rfl fun c hc => by rw [hoth c (Finset.ne_of_mem_erase hc)]
  rw [hrest, add_left_inj] at hxl
  have hmod : ((shCell (zcode p) C ς x c0 (K' + 1) : ℕ) : ZMod p) = ((n c0 : ℕ) : ZMod p) :=
    mul_left_cancel₀ (hv c0) hxl
  rw [ZMod.natCast_eq_natCast_iff'] at hmod
  intro c
  by_cases hc : c = c0
  · subst hc
    rw [← Nat.div_add_mod (shCell (zcode p) C ς x c0 (K' + 1)) p, hdiv, hmod, Nat.div_add_mod]
  · exact hoth c hc

/-- **`lem:shift`(b)** for the residue sequence `R_v = resSeq a θ v`: for every digital shift `ς` and every `K ≥ 1`,
the fine cells occupied by the shifted prefix `P_{sK-1}` are exactly the `n̂ ∈ [0, p^K)^s` with
`∑_c v_c n̂_c ≡ ∑_c v_c ς_{c,K-1}`, each holding one point, and `sep(P_{sK-1}) ≥ p^{-1/s} L` for every lower bound `L`
of `‖(|b| - 𝟏)_+‖_2` on `Λ_v \ {0}`. -/
theorem shift_residue (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (ς : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K)
    (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) :
    (fun x c => shCell (zcode p) (resSeq a θ v) ς x c K) '' Set.Iio (p ^ (s * K - 1)) =
      {n : Fin s → ℕ | (∀ c, n c < p ^ K) ∧ ∑ c, v c * ((n c : ℕ) : ZMod p) = ∑ c, v c * ς c (K - 1)} ∧
    Set.InjOn (fun x c => shCell (zcode p) (resSeq a θ v) ς x c K) (Set.Iio (p ^ (s * K - 1))) ∧
    SepAtPrefix p s (s * K - 1) (shPoint (zcode p) (resSeq a θ v) ς) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  have hseq := resSeq_t0 (zcode p) a ha θ hθ v hv
  have hsh := (shift_seq0 (zcode p) _ ς).mpr hseq
  have hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) (resSeq a θ v) x c (K - 1) = 0 :=
    fun x hx => resSeq_skel_seq (zcode p) a ha θ v hv K hK (by omega) x hx
  refine ⟨Set.ext fun n => ⟨?_, ?_⟩, fun x hx y hy hxy => ?_, shift_skel_sep hs _ hseq ς v L hL K hK hskel⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun c => shCell_lt _ _ _ _ _, shift_skel_rel _ ς v K hK hskel x hx⟩
  · rintro ⟨hn, hrel⟩
    obtain ⟨x, hx, hxn⟩ := skel_surj_sh hs _ ς hsh v hv K hK hskel n hn hrel
    exact ⟨x, hx, funext hxn⟩
  · exact skel_inj_sh hs _ ς hsh K hK x y hx hy fun c => congrFun hxy c

end GeoSeq
