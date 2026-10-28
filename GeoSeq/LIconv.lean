/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.LIa
public import GeoSeq.N2

@[expose] public section

/-!
# GeoSeq stage S11: the converse in dimension two (`prop:LIconv`) and `prop:N2`(a) for level-invariant laws

* `vecDigit_scrGen`: the digits of an index vector are the digit functionals of its polynomial.
* `law_scr` (the level-`K` law of an arbitrary scramble of the Faure frame, from `lem:ebasis`) and
  `carry_val` (the carry responses `D(l)` are partial sums of its coefficients).
* **`LIconv`** (`prop:LIconv`): `q` odd or `q = 2`, a scramble of the Faure frame with a level-invariant law
  is self-similar with one common scale `θ`, and `X^{(1)}_{0←1} X^{(1)}_{1←0} = θ²`.
* **`N2a_LI`** (`prop:N2`(a), level-invariant clause).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-! ## Index vectors as polynomials -/

/-- The index polynomial `V(z) = ∑_k V_k z^k` of an index vector. -/
noncomputable def vpoly {m : ℕ} (V : Fin m → F) : F[X] := ∑ k : Fin m, Polynomial.monomial k (V k)

lemma vpoly_coeff {m : ℕ} (V : Fin m → F) (j : ℕ) :
    (vpoly V).coeff j = if h : j < m then V ⟨j, h⟩ else 0 := by
  rw [vpoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro k _ hk; rw [ite_eq_right]; intro hkj; exact hk (Fin.ext hkj)
    · simp
  · exact Finset.sum_eq_zero fun k _ => ite_eq_right (fun hkj => absurd (hkj ▸ k.isLt) h)

lemma vpoly_natDegree {m : ℕ} (hm : 1 ≤ m) (V : Fin m → F) : (vpoly V).natDegree < m := by
  have : (vpoly V).natDegree ≤ m - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [vpoly_coeff, dite_eq_right (by norm_cast at hN; omega)]
  omega

/-- The digits of an index vector are the digit functionals of its index polynomial. -/
lemma vecDigit_scrGen {s m : ℕ} (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (V : Fin m → F) (c : Fin s)
    (n : ℕ) : vecDigit (scrGen a L) V c n = scrDig (a c) (L c) n (vpoly V) := by
  rw [vecDigit, scrDig]
  simp only [scrGen, vpoly, map_sum, Polynomial.finsetSum_coeff, taylor_monomial_coeff,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-! ## The law of an arbitrary scramble and its carry responses -/

/-- The own coefficients `-F^{(c)}_j / F^{(c)}_K` of `lem:ebasis`(ii). -/
noncomputable def ownC (B : Fin 2 → ℕ → ℕ → F) (c : Fin 2) (K j : ℕ) : F :=
  -(∑ n ∈ range (K - j + 1), coeff n (gamF : PS) * B c (K - n) j) / B c K K

/-- The cross coefficients `-T_c[K][K] B_{c'}[K-1][j]` of `lem:ebasis`(i). -/
noncomputable def crossC (B : Fin 2 → ℕ → ℕ → F) (c c' : Fin 2) (K j : ℕ) : F :=
  -(B c' (K - 1) j) / B c K K

/-- The level-`K` law of an arbitrary scramble of the Faure frame on index vectors (`lem:ebasis`). -/
lemma law_scr (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (K : ℕ) (hK : 1 ≤ K) (c c' : Fin 2) (hcc : c' ≠ c) (V : Fin (2 * K) → F) :
    vecDigit (scrGen faurePl L) V c K =
      ∑ j ∈ range K, ownC B c K j * vecDigit (scrGen faurePl L) V c j +
        ∑ j ∈ range K, crossC B c c' K j * vecDigit (scrGen faurePl L) V c' j := by
  simp only [vecDigit_scrGen, ownC, crossC]
  exact ebasis L B hB K hK (vpoly V) (vpoly_natDegree (by omega) V) c c' hcc

lemma carryPat_sum (K l : ℕ) (c₂ c₁ : Fin 2) (x : ℕ → F) :
    ∑ j ∈ range K, x j * carryPat K l c₂ c₁ j =
      if c₁ = c₂ then ∑ j ∈ range K, (if K - l ≤ j then x j else 0) else 0 := by
  split_ifs with h
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp only [carryPat, h, true_and]
    have : j < K := by simpa using hj
    split_ifs <;> simp_all
  · exact Finset.sum_eq_zero fun j _ => by simp [carryPat, h]

/-- **Carry responses of an arbitrary scramble**: `D(l)[c][c₂] = ∑_{K-l ≤ j < K}` (coefficient of
`y_{c₂,j}` in `r_c`). -/
lemma carry_val (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (K : ℕ) (hK : 1 ≤ K) (l : ℕ) (c c' : Fin 2) (hcc : c' ≠ c) (c₂ : Fin 2) (d : F)
    (hd : IsCarryEntry (scrGen faurePl L) K 0 l c c₂ d) :
    d = ∑ j ∈ range K, (if K - l ≤ j then (if c₂ = c then ownC B c K j else crossC B c c' K j)
      else 0) := by
  obtain ⟨V, hV⟩ := hd.1
  have h := hd.2 V hV
  rw [add_zero, law_scr L B hB K hK c c' hcc V] at h
  have e1 : ∑ j ∈ range K, ownC B c K j * vecDigit (scrGen faurePl L) V c j =
      ∑ j ∈ range K, ownC B c K j * carryPat K l c₂ c j :=
    Finset.sum_congr rfl (fun j hj => by rw [hV c j (by simpa using hj)])
  have e2 : ∑ j ∈ range K, crossC B c c' K j * vecDigit (scrGen faurePl L) V c' j =
      ∑ j ∈ range K, crossC B c c' K j * carryPat K l c₂ c' j :=
    Finset.sum_congr rfl (fun j hj => by rw [hV c' j (by simpa using hj)])
  rw [← h, e1, e2, carryPat_sum, carryPat_sum]
  by_cases h2 : c₂ = c
  · subst h2; simp [hcc]
  · have : c₂ = c' := by fin_cases c₂ <;> fin_cases c <;> fin_cases c' <;> simp_all
    subst this; simp [h2, Ne.symm h2]

/-- Successive differences of the partial sums: `S(n+1) - S(n) = x_{K-1-n}`. -/
lemma partial_diff (K n : ℕ) (hn : n < K) (x : ℕ → F) :
    ∑ j ∈ range K, (if K - (n + 1) ≤ j then x j else 0) -
      ∑ j ∈ range K, (if K - n ≤ j then x j else 0) = x (K - 1 - n) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (K - 1 - n)]
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), sub_zero]
  · intro j hj hjn
    have : j < K := by simpa using hj
    by_cases h1 : K - n ≤ j
    · rw [ite_eq_left (by omega), ite_eq_left h1, sub_self]
    · rw [ite_eq_right h1, ite_eq_right (by omega), sub_self]
  · intro h; simp at h; omega

/-! ## The converse (`prop:LIconv`) -/

/-- In a two-element field every nonzero element is `1`. -/
lemma eq_one_of_card_two [Fintype F] [DecidableEq F] (h : Fintype.card F = 2) (a : F) (ha : a ≠ 0) :
    a = 1 := by
  by_contra h1
  have hle : ({0, 1, a} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha]), Finset.card_pair (Ne.symm h1), h]
    at hle
  omega

/-- **`prop:LIconv`** (the converse in dimension two): let `q` be odd or `q = 2` (`2 ≠ 0` in `F`, or
`|F| = 2`). If the law of a scramble of the Faure frame (`a_0 = 0`, `a_1 = 1`, `L_c` lower triangular
with nonzero diagonal) is level-invariant, then the scramble is self-similar with one common scale
`θ ≠ 0`: `C_c = ssGen g (z_c(θx))` (`def:selfsim`) with multipliers `g_c(0) ≠ 0`. In particular
`X^{(1)}_{0←1} X^{(1)}_{1←0} = θ²` (the depth-0 cross responses at level `1`). -/
theorem LIconv [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0 ∨ Fintype.card F = 2)
    (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (hLI : LevelInv (scrGen faurePl L)) :
    ∃ θ : F, θ ≠ 0 ∧
      (∃ g : Fin 2 → PS, (∀ c, constantCoeff (g c) ≠ 0) ∧
        scrGen faurePl L = ssGen g (fun c => rescale θ (zF c))) ∧
      ∀ d01 d10 : F, IsCarryEntry (scrGen faurePl L) 1 0 1 0 1 d01 →
        IsCarryEntry (scrGen faurePl L) 1 0 1 1 0 d10 → d01 * d10 = θ ^ 2 := by
  obtain ⟨Dl, hDl⟩ := hLI
  obtain ⟨B, hB⟩ := ebas_B_exists L hL
  have hBd := B_diag_ne L B hB
  -- partial sums, with `D(0) = 0`
  obtain ⟨Dl', hD0, hDpos⟩ : ∃ D : ℕ → Fin 2 → Fin 2 → F, (∀ c c', D 0 c c' = 0) ∧
      ∀ l, 1 ≤ l → ∀ c c', D l c c' = Dl l c c' :=
    ⟨fun l c c' => if l = 0 then 0 else Dl l c c', fun _ _ => by simp,
      fun l hl _ _ => by simp [show l ≠ 0 by omega]⟩
  have hS : ∀ K, 1 ≤ K → ∀ l, l ≤ K → ∀ c c' c₂ : Fin 2, c' ≠ c →
      Dl' l c c₂ = ∑ j ∈ range K, (if K - l ≤ j then
        (if c₂ = c then ownC B c K j else crossC B c c' K j) else 0) := by
    intro K hK l hl c c' c₂ hcc
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [hD0]
      exact (Finset.sum_eq_zero fun j hj => by simp at hj; rw [ite_eq_right (by omega)]).symm
    · rw [hDpos l hl0]
      exact carry_val L B hB K hK l c c' hcc c₂ _ (hDl K l c c₂ hl0 hl)
  have hcoef : ∀ K, 1 ≤ K → ∀ n, n < K → ∀ c c' c₂ : Fin 2, c' ≠ c →
      (if c₂ = c then ownC B c K (K - 1 - n) else crossC B c c' K (K - 1 - n)) =
        Dl' (n + 1) c c₂ - Dl' n c c₂ := by
    intro K hK n hn c c' c₂ hcc
    rw [hS K hK (n + 1) (by omega) c c' c₂ hcc, hS K hK n (by omega) c c' c₂ hcc]
    exact (partial_diff K n hn (fun j => if c₂ = c then ownC B c K j else crossC B c c' K j)).symm
  obtain ⟨X, hX⟩ : ∃ X : ℕ → F, ∀ n, X n = Dl' (n + 1) 0 1 - Dl' n 0 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X : ℕ → F, ∀ n, X n = Dl' (n + 1) 1 0 - Dl' n 1 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → F, ∀ K, b K = B 0 K K := ⟨_, fun _ => rfl⟩
  have hb0 : ∀ K, b K ≠ 0 := fun K => by rw [hb]; exact hBd 0 K
  -- Step 1: the cross law of coordinate `0` fixes `B_1` up to the diagonal of `T_0`
  have step1 : ∀ i j, j ≤ i → B 1 i j = -X (i - j) * b (i + 1) := by
    intro i j hji
    have h := hcoef (i + 1) (by omega) (i - j) (by omega) 0 1 1 (by decide)
    rw [ite_eq_right (by decide), crossC, show i + 1 - 1 - (i - j) = j by omega,
      show i + 1 - 1 = i by omega, ← hX, div_eq_iff (hBd 0 (i + 1))] at h
    rw [hb]; linear_combination (-1 : F) * h
  have step1' : ∀ i j, j ≤ i → B 0 i j = -X' (i - j) * B 1 (i + 1) (i + 1) := by
    intro i j hji
    have h := hcoef (i + 1) (by omega) (i - j) (by omega) 1 0 0 (by decide)
    rw [ite_eq_right (by decide), crossC, show i + 1 - 1 - (i - j) = j by omega,
      show i + 1 - 1 = i by omega, ← hX', div_eq_iff (hBd 1 (i + 1))] at h
    linear_combination (-1 : F) * h
  have hX0 : X 0 ≠ 0 := by
    intro h0; have := step1 0 0 le_rfl; rw [h0, neg_zero, zero_mul] at this; exact hBd 1 0 this
  have hX'0 : X' 0 ≠ 0 := by
    intro h0; have := step1' 0 0 le_rfl; rw [h0, neg_zero, zero_mul] at this; exact hBd 0 0 this
  -- Step 2: the own law of coordinate `1` at depth one fixes the diagonal
  have step2 : ∀ K, 1 ≤ K → 2 * X 0 * b K = -(Dl' 1 1 1 * X 0 + X 1) * b (K + 1) := by
    intro K hK
    have h := hcoef K hK 0 hK 1 0 1 (by decide)
    rw [ite_eq_left rfl, hD0, sub_zero, Nat.sub_zero] at h
    have hown : ownC B 1 K (K - 1) = -(B 1 K (K - 1) + 2 * B 1 (K - 1) (K - 1)) / B 1 K K := by
      rw [ownC, show K - (K - 1) + 1 = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one,
        gamF_zero, gamF_one, Nat.sub_zero, show K - 1 = K - 1 from rfl, one_mul]
    rw [hown, step1 K (K - 1) (by omega), step1 (K - 1) (K - 1) le_rfl, step1 K K le_rfl,
      show K - (K - 1) = 1 by omega, show K - 1 + 1 = K by omega] at h
    simp only [Nat.sub_self, zero_add] at h
    rw [div_eq_iff (mul_ne_zero (neg_ne_zero.2 hX0) (hb0 (K + 1)))] at h
    linear_combination h
  have hθ : ∃ θ : F, θ ≠ 0 ∧ ∀ K, 1 ≤ K → b K = θ * b (K + 1) := by
    rcases h2 with h2 | h2
    · have hκ : -(Dl' 1 1 1 * X 0 + X 1) ≠ 0 := by
        intro h0; have := step2 1 le_rfl; rw [h0, zero_mul] at this
        exact mul_ne_zero (mul_ne_zero h2 hX0) (hb0 1) this
      refine ⟨-(Dl' 1 1 1 * X 0 + X 1) / (2 * X 0), div_ne_zero hκ (mul_ne_zero h2 hX0),
        fun K hK => ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero h2 hX0)]
      linear_combination step2 K hK
    · refine ⟨1, one_ne_zero, fun K _ => ?_⟩
      rw [eq_one_of_card_two h2 _ (hb0 K), eq_one_of_card_two h2 _ (hb0 (K + 1)), one_mul]
  obtain ⟨θ, hθ0, hθb⟩ := hθ
  have hbθ : ∀ i, b (i + 1) = b 1 * (θ ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h := hθb (i + 1) (by omega)
      rw [ih] at h
      have hθi : θ ^ i ≠ 0 := pow_ne_zero _ hθ0
      rw [pow_succ, mul_inv, ← mul_assoc, eq_mul_inv_iff_mul_eq₀ hθ0]
      field_simp at h ⊢
      linear_combination -h
  -- Steps 3 and 4: the e-basis form of both coordinates
  have form1 : ∀ i j, j ≤ i → B 1 i j = -b 1 * (θ ^ i)⁻¹ * coeff (i - j) (PowerSeries.mk X) := by
    intro i j hji
    rw [step1 i j hji, hbθ, coeff_mk]; ring
  have form0 : ∀ i j, j ≤ i →
      B 0 i j = (b 1 * X 0 * θ⁻¹) * (θ ^ i)⁻¹ * coeff (i - j) (PowerSeries.mk X') := by
    intro i j hji
    rw [step1' i j hji, form1 (i + 1) (i + 1) le_rfl, Nat.sub_self, coeff_mk, coeff_mk, pow_succ,
      mul_inv]
    ring
  obtain ⟨g0, hg0, hg0s⟩ := LI_a_B L B hB θ hθ0 0 (b 1 * X 0 * θ⁻¹)
    (mul_ne_zero (mul_ne_zero (hb0 1) hX0) (inv_ne_zero hθ0)) (PowerSeries.mk X')
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; exact hX'0) form0
  obtain ⟨g1, hg1, hg1s⟩ := LI_a_B L B hB θ hθ0 1 (-b 1) (neg_ne_zero.2 (hb0 1))
    (PowerSeries.mk X) (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; exact hX0) form1
  refine ⟨θ, hθ0, ⟨![g0, g1], fun c => by fin_cases c <;> simpa, ?_⟩, ?_⟩
  · rw [scrGen_eq_ssGen_iff]
    intro c n V
    fin_cases c
    · exact hg0s n V
    · exact hg1s n V
  · intro d01 d10 h01 h10
    have e01 : d01 = X 0 := by
      rw [carryEntry_unique _ _ _ _ _ _ h01 (hDl 1 1 0 1 le_rfl le_rfl), hX, hD0, sub_zero,
        hDpos 1 le_rfl]
    have e10 : d10 = X' 0 := by
      rw [carryEntry_unique _ _ _ _ _ _ h10 (hDl 1 1 1 0 le_rfl le_rfl), hX', hD0, sub_zero,
        hDpos 1 le_rfl]
    have h11 := step1' 1 1 le_rfl
    rw [form1 2 2 le_rfl, ← hb, Nat.sub_self, coeff_mk] at h11
    have hb1' := hb0 1
    rw [e01, e10]
    field_simp at h11
    linear_combination -h11

/-- **`prop:N2`(a), level-invariant clause**: for `q` odd or `q = 2`, if the law of a scramble of the
Faure frame is level-invariant, the own responses `D(l)[1][1]` and the cross responses `D(l)[0][1]`
(at every level) have generating functions that are not both rational. -/
theorem N2a_LI [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0 ∨ Fintype.card F = 2)
    (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (hLI : LevelInv (scrGen faurePl L))
    (o x : ℕ → F)
    (ho : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (scrGen faurePl L) K 0 l 1 1 (o l))
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (scrGen faurePl L) K 0 l 0 1 (x l)) :
    ¬ (IsRatPS (PowerSeries.mk o) ∧ IsRatPS (PowerSeries.mk x)) := by
  obtain ⟨θ, hθ, ⟨g, hg, hss⟩, -⟩ := LIconv h2 L hL hLI
  have hgf : g = ![g 0, g 1] := by funext c; fin_cases c <;> rfl
  have hzf : (fun c => rescale θ (zF c) : Fin 2 → PS) =
      ![rescale θ (zF 0), rescale θ (zF 1)] := by funext c; fin_cases c <;> rfl
  rw [hss, hgf, hzf] at ho hx
  refine N2a θ hθ _ _ (g 0) (g 1) ?_ ?_ ?_ (hg 0) (hg 1) o x ho hx
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
    simp [zF, constantCoeff_tRoot]
  · rw [← map_add]; simp [zF]
  · rw [← map_mul, show (zF 0 * zF 1 : PS) = -(tRoot + tRoot ^ 2) by simp [zF]; ring,
      tRoot_add_sq, map_neg, rescale_X]

end GeoSeq
