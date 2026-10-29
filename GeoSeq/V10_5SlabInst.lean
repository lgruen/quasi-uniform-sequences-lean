/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_5Slab
public import GeoSeq.V94Thm
public import GeoSeq.V96Sep
public import GeoSeq.V97Shift
public import GeoSeq.V9Thm

@[expose] public section

/-!
# GeoSeq stage V10-5 (part 3): `prop:liftslab`(ii) — the three in-slab bounds

`lem:shift` transfers the certificate of `lem:cert` to every digitally shifted copy (`cert_shift`, V7). The one-digit
and one-row forms used by `thm:residuestar` and `thm:block` are rerun on the shifted digits (`cert_prime_shift`,
`cert_one_shift`, `cert_row_shift`), which gives the shifted forms of the two theorems (`residuestar_sep_shift`,
`block_sep_shift`); `thm:residue` has its shifted form `shift_residue` (V9-7). With `slab_sep`:

* **`slab_residuestar`**: staggered residue sequence `𝓡^⋆_v` (`thm:residuestar`, `p ≥ 5`), `m = (s+1)K`, `K_0 = K`:
  two points of one slab are at distance `≥ β(k) N^{-1/(s+1)}`;
* **`slab_residue`**: residue sequence `𝓡_v` (`thm:residue`), `m = (s+1)K - 1`, `K_0 = K`: `≥ p^{-1/(s+1)} L N^{-1/(s+1)}`
  for every lower bound `L` of `‖(|b| - 𝟏)_+‖_2` on `Λ_v ∖ {0}`, in particular `L = ℓ_jit(Λ_v)` (`slab_residue_ljit`);
* **`slab_block`**: block-periodic sequence (`thm:block`, `ℓ = s`), `m = s(s+1)K`, `K_0 = sK`: `≥ min(1, LB) N^{-1/(s+1)}`
  for every `LB` below the one-digit relaxation (the `LB(F)` of `thm:block`).
-/

namespace GeoSeq

open Finset Polynomial

section Cert

variable {q s : ℕ} [NeZero q]

/-- `lem:cert` over `ℤ/qℤ` (responses without the `l = 0` convention) for the shifted sequence. -/
theorem cert_prime_shift (C : Gen s (ZMod q)) (ς : Fin s → ℕ → ZMod q) (K j : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l → LB ≤ certTerm (zcode q) j e (certSigmaP Dr j e l)) :
    SepAtLevel q s K (shPoint (zcode q) C ς) (min 1 LB) := by
  classical
  set Dr' : ℕ → ℕ → Fin s → Fin s → ZMod q := fun i l c c' => if l = 0 then 0 else Dr i l c c'
    with hDr'
  refine cert_shift (zcode q) C ς K j hK hnet Dr' (fun i c c' => by simp [hDr']) ?_ LB ?_
  · intro i hi l hl hlK c c'
    have : Dr' i l c c' = Dr i l c c' := by simp [hDr', show l ≠ 0 by omega]
    rw [this]; exact hD i hi l hl hlK c c'
  · intro e l hst y
    have hσ : certSigma (zcode q) Dr' j e l y = certSigmaP Dr j e l := by
      funext c i
      unfold certSigma certSigmaP carryChange
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [digInc_zcode, digInc_zcode]
      have : Dr' i (l c') c c' = Dr i (l c') c c' := by
        simp [hDr', show l c' ≠ 0 by have := hst.2.2 c'; omega]
      rw [this]; ring
    rw [hσ]; exact hLB e l hst

/-- `lem:cert` with one geometric digit for the shifted sequence. -/
theorem cert_one_shift (C : Gen s (ZMod q)) (ς : Fin s → ℕ → ZMod q) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 q (e c) (∑ c', (e c' : ZMod q) * Dr (l c') c c') : ℝ) / q) ^ 2)) :
    SepAtLevel q s K (shPoint (zcode q) C ς) (min 1 LB) := by
  refine cert_prime_shift C ς K 1 hK hnet (fun _ l c c' => Dr l c c') ?_ LB ?_
  · intro i hi l hl hlK c c'
    obtain rfl : i = 0 := by omega
    exact hD l hl hlK c c'
  · intro e l hst
    refine (hLB e l hst).trans_eq ?_
    unfold certTerm
    simp only [gapNum_one, pow_one]
    rfl

/-- The one-row certificate for the shifted sequence. -/
theorem cert_row_shift (C : Gen s (ZMod q)) (ς : Fin s → ℕ → ZMod q) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (c₀ : Fin s) (Drow : ℕ → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c', IsCarryEntry C K 0 l c₀ c' (Drow l c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ (gapNum1 q (e c₀) (∑ c', (e c' : ZMod q) * Drow (l c') c') : ℝ) / q) :
    SepAtLevel q s K (shPoint (zcode q) C ς) (min 1 LB) := by
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
  refine cert_one_shift C ς K hK hnet Dr hDr LB fun e l hst => ?_
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

end Cert

section Seqs

variable {s : ℕ} {p : ℕ} [Fact p.Prime]

/-- **`thm:residuestar` for every digitally shifted copy** (`lem:shift`): `sep(P_{sK}) ≥ β(k)`. -/
theorem residuestar_sep_shift (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (ς : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p s K (shPoint (zcode p) (resStar a θ cs μs k) ς) (betaStar p cs k) := by
  classical
  have hnet : BlockNet0 (zcode p) (resStar a θ cs μs k) (s * K) 0 :=
    resStar_t0 (zcode p) a ha θ hθ cs μs hμ k hk (s * K) 0
  have hq : 4 ≤ p ^ K := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hβp := betaStar_le_pred p hs cs k
  have hβ1 : betaStar p cs k ≤ 1 := hβp.trans (by rw [div_le_one hp0]; linarith)
  have h := cert_row_shift (resStar a θ cs μs k) ς K hq hnet cs (fun _ c' => if c' = cs then 0 else k c')
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

/-- **`thm:block`(iii) for every digitally shifted copy** (`lem:shift`): `sep(P_{sℓK}) ≥ min(1, LB)`. -/
theorem block_sep_shift (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (ς : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) (LB : ℝ)
    (hLB : ∀ e l, IsStep (ℓ * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2)) :
    SepAtLevel p s (ℓ * K) (shPoint (zcode p) (blockGen a θ ℓ v Fd Nd v') ς) (min 1 LB) := by
  have hs : 1 ≤ s := by omega
  have hnet := blockGen_t0 θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hv hv' hNd (s * (ℓ * K)) 0
  have hq : 4 ≤ p ^ (ℓ * K) := le_trans (by
    have := (Fact.out : p.Prime).two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left this 2) (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by
        have : ℓ ≤ ℓ * K := Nat.le_mul_of_pos_right _ (by omega)
        omega))
  exact cert_one_shift _ ς (ℓ * K) hq hnet (fun l i c' => ∑ n ∈ range (min l (s - 1)), Fd n i c')
    (fun l hl hlK i c' => blockGen_carry a θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hrel hv K hK hnet l hl hlK i c')
    LB hLB

omit [Fact p.Prime] in
/-- `((p^K)^{s+1})^{-1/(s+1)} = p^{-K}`. -/
lemma lift_scale (hp : 0 < p) (s K : ℕ) :
    ((p : ℝ) ^ ((s + 1) * K)) ^ (-(1 / ((s : ℝ) + 1))) = ((p : ℝ) ^ K)⁻¹ := by
  have hs1 : ((s : ℝ) + 1) ≠ 0 := by positivity
  rw [mul_comm, pow_mul, ← Real.rpow_natCast ((p : ℝ) ^ K), ← Real.rpow_mul (by positivity)]
  push_cast
  rw [show ((s : ℝ) + 1) * -(1 / ((s : ℝ) + 1)) = -1 by field_simp, Real.rpow_neg_one]

/-- **`prop:liftslab`(ii), staggered residue sequence**: in the lift `P̂_m` of `𝓡^⋆_v` (`thm:residuestar`, `p ≥ 5`) at
`m = (s+1)K`, two distinct points of one slab with `K_0 = K` are at distance `≥ β(k) N^{-1/(s+1)}`. -/
theorem slab_residuestar (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hxy : x / p ^ ((s + 1) * K - K) = y / p ^ ((s + 1) * K - K)) (hne : x ≠ y) :
    betaStar p cs k * ((p : ℝ) ^ ((s + 1) * K)) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (resStar a θ cs μs k) ((s + 1) * K) x)
        (liftPt (zcode p) (resStar a θ cs μs k) ((s + 1) * K) y) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  rw [lift_scale hp0, ← div_eq_mul_inv]
  refine slab_sep (zcode p) (resStar a θ cs μs k) ((s + 1) * K) K _ ?_ x y hxy hne
  intro b u w hu hw huw
  have hm : (s + 1) * K - K = s * K := by rw [add_mul, one_mul, Nat.add_sub_cancel]
  rw [hm] at hu hw
  rw [div_le_iff₀ hpK, mul_comm]
  exact residuestar_sep_shift hp hs a ha θ hθ cs μs hμ k hk _ K hK u w hu hw huw

/-- **`prop:liftslab`(ii), residue sequence**: in the lift of `𝓡_v` (`thm:residue`) at `m = (s+1)K - 1`, two distinct
points of one slab with `K_0 = K` are at distance `≥ p^{-1/(s+1)} L N^{-1/(s+1)}`, for every lower bound `L` of
`‖(|b| - 𝟏)_+‖_2` on `Λ_v ∖ {0}`. -/
theorem slab_residue (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0)
    (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b)
    (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hxy : x / p ^ ((s + 1) * K - 1 - K) = y / p ^ ((s + 1) * K - 1 - K)) (hne : x ≠ y) :
    (p : ℝ) ^ (-(1 / ((s : ℝ) + 1))) * L * ((p : ℝ) ^ ((s + 1) * K - 1)) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) x)
        (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) y) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hsc := prefix_scale hp0 (s := s + 1) (by omega) K hK
  have hsc' := prefix_scale hp0 (s := s) (by omega) K hK
  push_cast at hsc
  have e : (p : ℝ) ^ (-(1 / ((s : ℝ) + 1))) * L * ((p : ℝ) ^ ((s + 1) * K - 1)) ^ (-(1 / ((s : ℝ) + 1))) =
      (p : ℝ) ^ (-(1 / (s : ℝ))) * L * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ))) := by
    rw [mul_comm _ L, mul_assoc, hsc, mul_comm _ L, mul_assoc, hsc']
  rw [e]
  refine slab_sep (zcode p) (resSeq a θ v) ((s + 1) * K - 1) K _ ?_ x y hxy hne
  intro b u w hu hw huw
  have hm : (s + 1) * K - 1 - K = s * K - 1 := by rw [add_mul, one_mul]; omega
  rw [hm] at hu hw
  exact (shift_residue hs a ha θ hθ v hv _ K hK L hL).2.2 u w hu hw huw

/-- `prop:liftslab`(ii) for the residue sequence with `L = ℓ_jit(Λ_v)` (the constant written in the paper). -/
theorem slab_residue_ljit (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hxy : x / p ^ ((s + 1) * K - 1 - K) = y / p ^ ((s + 1) * K - 1 - K)) (hne : x ≠ y) :
    (p : ℝ) ^ (-(1 / ((s : ℝ) + 1))) * ljit v * ((p : ℝ) ^ ((s + 1) * K - 1)) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) x)
        (liftPt (zcode p) (resSeq a θ v) ((s + 1) * K - 1) y) :=
  slab_residue hs a ha θ hθ v hv (ljit v) (fun b hb hlat => ljit_le v b hb hlat) K hK x y hxy hne

/-- **`prop:liftslab`(ii), block-periodic sequence** (`thm:block`, period `ℓ = s`): in the lift at `m = s(s+1)K`,
two distinct points of one slab with `K_0 = sK` are at distance `≥ min(1, LB) N^{-1/(s+1)}` for every `LB` below the
one-digit relaxation of the design (the `LB(F)` of `thm:block`). -/
theorem slab_block (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0)
    (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (s - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (s - 1 - n))
    (K : ℕ) (hK : 1 ≤ K) (LB : ℝ)
    (hLB : ∀ e l, IsStep (s * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2))
    (x y : ℕ) (hxy : x / p ^ ((s + 1) * (s * K) - s * K) = y / p ^ ((s + 1) * (s * K) - s * K)) (hne : x ≠ y) :
    min 1 LB * ((p : ℝ) ^ ((s + 1) * (s * K))) ^ (-(1 / ((s : ℝ) + 1))) ≤
      Z3NetDGS.torDist2 (liftPt (zcode p) (blockGen a θ s v Fd Nd v') ((s + 1) * (s * K)) x)
        (liftPt (zcode p) (blockGen a θ s v Fd Nd v') ((s + 1) * (s * K)) y) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpK : (0 : ℝ) < (p : ℝ) ^ (s * K) := by positivity
  rw [lift_scale hp0, ← div_eq_mul_inv]
  refine slab_sep (zcode p) (blockGen a θ s v Fd Nd v') ((s + 1) * (s * K)) (s * K) _ ?_ x y hxy hne
  intro b u w hu hw huw
  have hm : (s + 1) * (s * K) - s * K = s * (s * K) := by rw [add_mul, one_mul, Nat.add_sub_cancel]
  rw [hm] at hu hw
  rw [div_le_iff₀ hpK, mul_comm]
  exact block_sep_shift a ha θ hθ s le_rfl hs2 v hv Fd Nd v' hv' hNd hrel _ K hK LB hLB u w hu hw huw

end Seqs

end GeoSeq
