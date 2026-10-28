/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V97Shift
public import GeoSeq.V3Cap
public import GeoSeq.V9Kor

@[expose] public section

/-!
# GeoSeq stage V9-7 (part 4): windows and corrected skeleton relations (`prop:joint`)

The scramble is the residue-type generator `ssResGen a θ N U` (local multiplier `φ_c = N_c / U_c`, rational) with
correction coefficients `χ` (`CorrTrunc`, `lem:corrS`), as in `GeoSeq.V97Corr`.

* **`joint_col`**, **`joint_step`** (**`prop:joint`(i)**): at a full level `K` the carry responses `D(l)` (`IsCarryEntry`)
  satisfy `∑_c v_c D(l)[c][c'] = -v_{c'} Ψ_{c'}(l)`; for a step `e` with carry lengths `l_c`,
  `∑_c v_c σ_c = -∑_c e_c v_c Ψ_c(l_c)`.
* **`joint_transfer`** (**`prop:joint`(ii)**, one factor): replacing `φ_c` by `φ_c (1 + ε w^j)`, `j ≥ l`, leaves the cross
  responses `X^{(l)}_{c'←c}` unchanged and keeps `O^{(l)}_c + Ψ_c(l)`.
* **`joint_window`**, **`joint_minkowski`**, **`joint_iii`** (**`prop:joint`(iii)**): under the joint covering condition
  `Wo^{(c)} + [0, B] = 𝔽_p` the window bound is `≤ √s B / p`; if `ℓ_jit^{(B)}(Λ_v) > 0` then `B + 1 < ⌊p^{1/s}⌋ ≤ p^{1/s}`.
-/

namespace GeoSeq

open Finset Polynomial

section Resp

variable {F : Type*} [Field F] {s : ℕ}

/-- The index vector `V ∈ F^m` extended by `0`. -/
def vext {m : ℕ} (V : Fin m → F) (j : ℕ) : F := if h : j < m then V ⟨j, h⟩ else 0

lemma vecDigit_vext {m : ℕ} (C : Gen s F) (V : Fin m → F) (c : Fin s) (n : ℕ) :
    ∑ j ∈ range m, C c n j * vext V j = vecDigit C V c n := by
  unfold vecDigit
  rw [← Fin.sum_univ_eq_sum_range (fun j => C c n j * vext V j) m]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [vext, k.isLt]

lemma corr_carry_sum (χ : Fin s → ℕ → F) (K l : ℕ) (hlK : l ≤ K) (c c' : Fin s) :
    ∑ d ∈ Finset.Ico 1 (K + 1), χ c d * (carryPat K l c' c (K - d) : F) =
      if c = c' then psiSum χ c' l else 0 := by
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl]
    have h1 : ∀ d ∈ Finset.Ico 1 (K + 1), χ c d * (carryPat K l c c (K - d) : F) =
        if d ≤ l then χ c d else 0 := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      rw [carryPat_self K l c (by omega)]
      split_ifs <;> first | (exfalso; omega) | simp
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    unfold psiSum
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  · rw [if_neg hc]
    exact Finset.sum_eq_zero fun d _ => by rw [carryPat_ne K l hc, mul_zero]

/-- **`prop:joint`(i), column form**: at the full level `K`, if `χ` are the correction coefficients up to order `K + 1`,
the carry responses of column `c'` with carry length `l ∈ [1, K]` satisfy `∑_c v_c D(l)[c][c'] = -v_{c'} Ψ_{c'}(l)`. -/
theorem joint_col (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U : Fin s → F[X]) (hU : ∀ c, (U c).eval (a c) ≠ 0) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K) (htr : CorrTrunc a θ N U v χ (K + 1))
    (l : ℕ) (hlK : l ≤ K) (c' : Fin s) (Dl : Fin s → F)
    (hD : ∀ c, IsCarryEntry (ssResGen a θ N U) K 0 l c c' (Dl c)) :
    ∑ c, v c * Dl c = -(v c' * psiSum χ c' l) := by
  obtain ⟨V, hV⟩ := (hD c').1
  have hcor := ssRes_corr hs a ha θ hθ N U hU v χ hχ0 (K + 1) (by omega) htr (vext V) (s * K)
    (by rw [Nat.mul_succ]; omega)
  simp only [Nat.add_sub_cancel, vecDigit_vext] at hcor
  have hown : ∀ c, vecDigit (ssResGen a θ N U) V c K = Dl c := fun c => by
    have := (hD c).2 V hV; rwa [Nat.add_zero] at this
  have hcell : ∀ c, ∀ d ∈ Finset.Ico 1 (K + 1), χ c d * vecDigit (ssResGen a θ N U) V c (K - d) =
      χ c d * (carryPat K l c' c (K - d) : F) := fun c d hd => by
    rw [Finset.mem_Ico] at hd; rw [hV c (K - d) (by omega)]
  have hsum : ∀ c, v c * (vecDigit (ssResGen a θ N U) V c K + ∑ d ∈ Finset.Ico 1 (K + 1),
      χ c d * vecDigit (ssResGen a θ N U) V c (K - d)) = v c * Dl c + if c = c' then v c' * psiSum χ c' l else 0 :=
    fun c => by
      rw [Finset.sum_congr rfl (hcell c), corr_carry_sum χ K l hlK c c', hown c, mul_add]
      split_ifs with h
      · rw [h]
      · rw [mul_zero]
  rw [Finset.sum_congr rfl fun c _ => hsum c, Finset.sum_add_distrib, Finset.sum_ite_eq' univ c'
    (fun _ => v c' * psiSum χ c' l), if_pos (mem_univ _)] at hcor
  linear_combination hcor

/-- **`prop:joint`(i)**: for every full level `K`, every step `e` and carry lengths `l_c ∈ [1, K]`, the changes
`σ_c = ∑_{c'} e_{c'} D(l_{c'})[c][c']` of the geometric digits satisfy `∑_c v_c σ_c = -∑_c e_c v_c Ψ_c(l_c)`. -/
theorem joint_step (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U : Fin s → F[X]) (hU : ∀ c, (U c).eval (a c) ≠ 0) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K) (htr : CorrTrunc a θ N U v χ (K + 1))
    (e : Fin s → ℤ) (lc : Fin s → ℕ) (hl : ∀ c, lc c ≤ K) (Dr : Fin s → Fin s → F)
    (hD : ∀ c c', IsCarryEntry (ssResGen a θ N U) K 0 (lc c') c c' (Dr c c')) :
    ∑ c, v c * ∑ c', (e c' : F) * Dr c c' = -∑ c, (e c : F) * (v c * psiSum χ c (lc c)) := by
  have hcol := fun c' => joint_col hs a ha θ hθ N U hU v χ hχ0 K hK htr (lc c') (hl c') c'
    (fun c => Dr c c') (fun c => hD c c')
  calc ∑ c, v c * ∑ c', (e c' : F) * Dr c c' = ∑ c', (e c' : F) * ∑ c, v c * Dr c c' := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = -∑ c, (e c : F) * (v c * psiSum χ c (lc c)) := by
        simp_rw [hcol]
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- **`prop:joint`(ii)** (one factor): replace the local multiplier `φ_c = N_c/U_c` by `φ_c (1 + ε w^j)` with `j ≥ l`
(the other coordinates unchanged), and the correction coefficients `χ_{c,j}` by `χ_{c,j} - εθ^j` (`corrTrunc_modify`).
Then at every level `K ≥ l` the cross responses `X^{(l)}_{c'←c}` (carry length `l` in coordinate `c`) are unchanged and
`O^{(l)}_c + Ψ_c(l)` is unchanged. -/
theorem joint_transfer (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (χ : Fin s → ℕ → F) (c : Fin s) (ε : F) (j K l : ℕ) (hl : 1 ≤ l) (hlj : l ≤ j) (hlK : l ≤ K)
    (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (ssResGen a θ N U) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (ssResGen a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U) K 0 l
      c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧
    Dnew c + psiSum (Function.update χ c (Function.update (χ c) j (χ c j - ε * θ ^ j))) c l =
      Dold c + psiSum χ c l := by
  set G := ssResGen a θ N U
  set G' := ssResGen a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U
  obtain ⟨V, hV⟩ := (hnew c).1
  have hmod : ∀ n, vecDigit G' V c n = vecDigit G V c n +
      if j ≤ n then ε * θ ^ j * vecDigit G V c (n - j) else 0 := fun n => by
    have := ssRes_modify a ha θ hθ N U c ε j (vext V) (s * K) n
    simp only [vecDigit_vext] at this
    exact this
  have hother : ∀ c₁, c₁ ≠ c → ∀ n, vecDigit G' V c₁ n = vecDigit G V c₁ n := fun c₁ h n => by
    unfold vecDigit G G'; rw [ssRes_modify_other a θ N U c c₁ h ε j]
  have hcell : ∀ c₁, ∀ n < K, vecDigit G V c₁ n = carryPat K l c c₁ n := by
    intro c₁
    by_cases hc : c₁ = c
    · subst hc
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro hn
        have h1 := hmod n
        rw [hV c₁ n hn] at h1
        have h2 : (if j ≤ n then ε * θ ^ j * vecDigit G V c₁ (n - j) else 0) = 0 := by
          split_ifs with hj
          · rw [ih (n - j) (by omega) (by omega), carryPat_self K l c₁ (by omega), if_neg (by omega), mul_zero]
          · rfl
        rw [h2, add_zero] at h1
        exact h1.symm
    · intro n hn
      rw [← hother c₁ hc n, hV c₁ n hn]
  have hO : ∀ c₁, Dold c₁ = vecDigit G V c₁ K := fun c₁ => by
    have := (hold c₁).2 V hcell; rw [Nat.add_zero] at this; exact this.symm
  have hN : ∀ c₁, Dnew c₁ = vecDigit G' V c₁ K := fun c₁ => by
    have := (hnew c₁).2 V hV; rw [Nat.add_zero] at this; exact this.symm
  refine ⟨fun c₁ h => by rw [hN, hO, hother c₁ h], ?_⟩
  rw [hN, hO, hmod K]
  unfold psiSum
  simp only [Function.update_self]
  rcases eq_or_lt_of_le hlj with hjl | hjl
  · subst hjl
    rw [if_pos hlK, hcell c (K - l) (by omega), carryPat_self K l c (by omega), if_pos le_rfl,
      Finset.sum_update_of_mem (by simp; omega), Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase _ (χ c) (show l ∈ Finset.Ico 1 (l + 1) by simp; omega)]
    ring
  · have hsame : ∑ d ∈ Finset.Ico 1 (l + 1), Function.update (χ c) j (χ c j - ε * θ ^ j) d =
        ∑ d ∈ Finset.Ico 1 (l + 1), χ c d :=
      Finset.sum_congr rfl fun d hd => by
        rw [Finset.mem_Ico] at hd; rw [Function.update_of_ne (by omega)]
    rw [hsame]
    split_ifs with hjK
    · rw [hcell c (K - j) (by omega), carryPat_self K l c (by omega), if_neg (by omega), mul_zero, add_zero]
    · rw [add_zero]

end Resp

section Win

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`prop:joint`(iii), window part**: if every column satisfies the joint covering condition `Wo^{(c)} + [0, B] = 𝔽_p`
(every `ξ ∈ 𝔽_p` is `ω + t` with `ω ∈ Wo^{(c)}`, `0 ≤ t ≤ B`) and the cross windows are nonempty, then every window
bound satisfies `LB(W) ≤ √s B / p`. -/
theorem joint_window (hs : 1 ≤ s) (W : Fin s → Fin s → Set (ZMod p)) (B : ℕ)
    (hcov : ∀ c (ξ : ZMod p), ∃ ω ∈ W c c, ∃ t : ℕ, t ≤ B ∧ ω + (t : ZMod p) = ξ)
    (hne : ∀ c c', c ≠ c' → (W c c').Nonempty) (LB : ℝ) (hLB : WinLB p W LB) :
    LB ≤ Real.sqrt s * B / p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set e : Fin s → ℤ := fun _ => 1
  have hσ : ∀ c, ∃ σ : ZMod p, σ ∈ sumsetS W e c ∧ gapNum1 p 1 σ ≤ B := by
    intro c
    let y : Fin s → ZMod p := fun c' => if h : c = c' then 0 else (hne c c' h).some
    obtain ⟨ω, hω, t, ht, hωt⟩ := hcov c (((B + 1 : ℕ) : ZMod p) - ∑ c' ∈ univ.erase c, y c')
    refine ⟨ω + ∑ c' ∈ univ.erase c, y c', ⟨Function.update y c ω, fun c' _ => ?_, ?_⟩, ?_⟩
    · by_cases h : c' = c
      · subst h; rw [Function.update_self]; exact hω
      · rw [Function.update_of_ne h]
        simp only [y, dif_neg (Ne.symm h)]
        exact (hne c c' (Ne.symm h)).some_mem
    · simp only [e, Int.cast_one, one_mul]
      rw [← Finset.add_sum_erase _ _ (mem_univ c), Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun c' hc' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hc')]
    · have hval : ω + ∑ c' ∈ univ.erase c, y c' = ((B + 1 - t : ℕ) : ZMod p) := by
        rw [Nat.cast_sub (by omega)]
        linear_combination hωt
      rw [hval]
      have h1 := gap1_add_one (p := p) ((B + 1 - t : ℕ) : ZMod p)
      have h2 := rep_le (p := p) ((B + 1 - t : ℕ) : ZMod p)
      by_cases hBp : B + 1 < p
      · have hne0 : ((B + 1 - t : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
        rw [if_neg hne0, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at h1
        omega
      · omega
  choose σ hσmem hσle using hσ
  have h := hLB e (fun _ => ⟨by norm_num, le_rfl⟩) ⟨⟨0, by omega⟩, one_ne_zero⟩ σ hσmem
  refine h.trans ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hterm : ∀ c, ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2 ≤ ((B : ℝ) / p) ^ 2 := fun c => by
    have : (gapNum1 p (e c) (σ c) : ℝ) ≤ B := by exact_mod_cast hσle c
    gcongr
  calc Real.sqrt (∑ c, ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2)
      ≤ Real.sqrt (∑ _c : Fin s, ((B : ℝ) / p) ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => hterm c)
    _ = Real.sqrt s * B / p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
        ring

/-- Minkowski's bound by pigeonhole: `Λ_v` (index `p` in `ℤ^s`) contains `b ≠ 0` with `‖b‖_∞ ≤ ⌊p^{1/s}⌋`. -/
lemma lat_small (hs : 1 ≤ s) (v : Fin s → ZMod p) :
    ∃ b : Fin s → ℤ, b ≠ 0 ∧ (∀ c, |b c| ≤ korRho p s) ∧ InLat v b := by
  set ρ := korRho p s
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin s → Fin (ρ + 1)) := by
    rw [ZMod.card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact lt_korRho_succ_pow hs
  obtain ⟨n, n', hnn, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin s → Fin (ρ + 1) => ∑ c, v c * (((n c : ℕ) : ℤ) : ZMod p)) hcard
  refine ⟨fun c => ((n c : ℕ) : ℤ) - ((n' c : ℕ) : ℤ), fun h => hnn ?_, fun c => ?_, ?_⟩
  · funext c
    have := congrFun h c
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact Fin.ext this
  · have h1 := (n c).isLt; have h2 := (n' c).isLt
    show |((n c : ℕ) : ℤ) - ((n' c : ℕ) : ℤ)| ≤ (ρ : ℤ)
    rw [abs_le]; constructor <;> omega
  · unfold InLat
    simp only [Int.cast_sub]
    exact sum_mul_sub_const univ v (fun c => (((n c : ℕ) : ℤ) : ZMod p)) (fun c => (((n' c : ℕ) : ℤ) : ZMod p)) _
      heq rfl

/-- **`prop:joint`(iii), Minkowski part**: if `ℓ_jit^{(B)}(Λ_v) > 0`, then `B + 1 < ⌊p^{1/s}⌋`. -/
theorem joint_minkowski (hs : 1 ≤ s) (B : ℕ) (v : Fin s → ZMod p) (hpos : 0 < ljitB B v) :
    B + 1 < korRho p s := by
  by_contra hcon
  obtain ⟨b, hb0, hbs, hlat⟩ := lat_small hs v
  have h0 : jitNormB B b = 0 := by
    unfold jitNormB
    rw [Finset.sum_eq_zero fun c _ => ?_, Real.sqrt_zero]
    have h1 : |(b c : ℝ)| ≤ (korRho p s : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast hbs c
    have h2 : (korRho p s : ℝ) ≤ B + 1 := by exact_mod_cast (by omega : korRho p s ≤ B + 1)
    rw [max_eq_right (by linarith)]; ring
  have := ljitB_le B v b hb0 hlat
  linarith

/-- **`prop:joint`(iii)**: under the joint covering condition with correction window `[0, B]`, `LB(W) ≤ √s B / p`; if
moreover `ℓ_jit^{(B)}(Λ_v) > 0` (so that `thm:corrected` with this `B` certifies a positive bound), then
`B < p^{1/s} - 1` and `LB(W) < √s (p^{1/s} - 1) / p`. -/
theorem joint_iii (hs : 1 ≤ s) (W : Fin s → Fin s → Set (ZMod p)) (B : ℕ)
    (hcov : ∀ c (ξ : ZMod p), ∃ ω ∈ W c c, ∃ t : ℕ, t ≤ B ∧ ω + (t : ZMod p) = ξ)
    (hne : ∀ c c', c ≠ c' → (W c c').Nonempty) (LB : ℝ) (hLB : WinLB p W LB) :
    LB ≤ Real.sqrt s * B / p ∧
      ∀ v : Fin s → ZMod p, 0 < ljitB B v →
        (B : ℝ) < (p : ℝ) ^ ((1 : ℝ) / s) - 1 ∧ LB < Real.sqrt s * ((p : ℝ) ^ ((1 : ℝ) / s) - 1) / p := by
  have h1 := joint_window hs W B hcov hne LB hLB
  refine ⟨h1, fun v hv => ?_⟩
  have hk := joint_minkowski hs B v hv
  have hfl : ((korRho p s : ℕ) : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / s) := Nat.floor_le (by positivity)
  have hk' : (B : ℝ) + 1 < korRho p s := by exact_mod_cast hk
  have hB : (B : ℝ) < (p : ℝ) ^ ((1 : ℝ) / s) - 1 := by linarith
  refine ⟨hB, h1.trans_lt ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsR : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < s))
  rw [div_lt_div_iff_of_pos_right hpR]
  exact mul_lt_mul_of_pos_left hB hsR

end Win

end GeoSeq
