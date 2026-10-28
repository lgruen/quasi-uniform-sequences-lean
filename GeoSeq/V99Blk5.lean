/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99Gen

@[expose] public section

/-!
# GeoSeq stage V9-9 (part 3): `thm:block`(c) for `s = 5` — algebra and the written bound

* `blk5a_injective`, `blk5v_ne`, `blk5_hrel` (identity (a) of `def:block`, every prime `p ≥ 5`, by evaluation at the
  places), `blk5_hNd` (vanishing orders), `blk5_hM` (partial sums), `blk5_dom` (diagonal dominance data).
* **`blk5_LB_proof`**: the written argument (diagonal dominance) for `p ≥ 5 a*_5 + 4 = 84`.
* `blk5_LB_chk`: the bound at one prime from one kernel evaluation of `caCheck` (the evaluations are in
  `V99Ca5a`–`V99Ca5f`, the assembly `blk5_block` in `V99Blk5Main`).
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

lemma blk5a_injective (hp : 5 ≤ p) : Function.Injective (blk5a (p := p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h4 : (4 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h21 : (2 : ZMod p) ≠ 1 := fun h => h1 (by linear_combination h)
  have h31 : (3 : ZMod p) ≠ 1 := fun h => h2 (by linear_combination h)
  have h32 : (3 : ZMod p) ≠ 2 := fun h => h1 (by linear_combination h)
  have h41 : (4 : ZMod p) ≠ 1 := fun h => h3 (by linear_combination h)
  have h42 : (4 : ZMod p) ≠ 2 := fun h => h2 (by linear_combination h)
  have h43 : (4 : ZMod p) ≠ 3 := fun h => h1 (by linear_combination h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [blk5a] at h ⊢ <;> (try field_simp at h) <;> simp_all

lemma blk5v_ne (hp : 5 ≤ p) (c : Fin 5) : blk5v (p := p) c ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h4 : (4 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  fin_cases c <;> simp [blk5v, h2, h3, h4]

set_option maxHeartbeats 4000000 in
lemma blk5_hev (hp : 5 ≤ p) : ∀ c i, i ≠ c → ∀ j, j ≠ c →
    (∏ i' : Fin 5, if i' = c ∨ i' = i then 1 else (blk5a (p := p) j - blk5a i')) =
      -(blk5v i) * ∑ n ∈ range (5 - 1), blockF blk5F n i c * ((blk5a j - blk5a c) ^ n *
        ∑ k ∈ range (5 - 1 - n), cfOf (s := 5) blk5cfL 24 c n k * blk5a j ^ k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h4 : (4 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h24 : (24 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  intro c i hic j hjc
  fin_cases c <;> fin_cases i <;> fin_cases j <;> simp at hic hjc ⊢ <;>
    simp [Fin.prod_univ_five, Finset.sum_range_succ, blk5a, blk5v, blockF, blk5F, cfOf, blk5cfL] <;>
    field_simp <;> norm_num

/-- **Identity (a) of `def:block` for `thm:block`(c), `s = 5`**, for every prime `p ≥ 5`. -/
theorem blk5_hrel (hp : 5 ≤ p) (c i : Fin 5) (h : i ≠ c) :
    wCoCo (blk5a (p := p)) c i = -C (blk5v i) *
      ∑ n ∈ range (5 - 1), C (blockF blk5F n i c) * blk5N c (5 - 1 - n) :=
  hrel_of_eval (by norm_num) _ (blk5a_injective hp) _ _ _ (blk5_hev hp) c i h

/-- The vanishing orders of the design numerators of `thm:block`(c), `s = 5` (every prime `p ≥ 5`). -/
theorem blk5_hNd (hp : 5 ≤ p) (c : Fin 5) (n : ℕ) (hn : n + 2 ≤ 5) :
    ∃ N', blk5N (p := p) c (5 - 1 - n) = (X - C (blk5a c)) ^ n * N' ∧ N'.eval (blk5a c) ≠ 0 := by
  refine hNd_of_ndPoly _ _ (fun c n hn => ?_) c n hn
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h4 : (4 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h24 : (24 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> fin_cases c <;>
    simp [Finset.sum_range_succ, blk5a, cfOf, blk5cfL] <;> (try field_simp) <;> (try norm_num) <;> smooth_ne hp

/-! ## The bound -/

/-- The diagonal `α = (16, 8, 12, 12, 7)` of `U*_5` (`F_0[c][c] = -α_c`, zero deeper diagonal). -/
def blk5α : Fin 5 → ℤ := ![16, 8, 12, 12, 7]

/-- The bounds `B_{ic} = max_j |M^{(j)}[i][c]|` of `U*_5` (diagonal `α`). -/
def blk5B : Fin 5 → Fin 5 → ℤ :=
  !![16, 6, 2, 2, 6; 2, 8, 3, 1, 2; 1, 6, 12, 2, 3; 1, 3, 2, 12, 6; 1, 2, 1, 3, 7]

lemma blk5_hM : ∀ j, j + 2 ≤ 5 → ∀ i c, blk5M j i c = ∑ n ∈ range (j + 1), blk5F n i c := by
  intro j hj; have : j ≤ 3 := by omega
  interval_cases j <;> decide +kernel

lemma blk5_diag : ∀ j, j + 2 ≤ 5 → ∀ i, blk5M j i i = -blk5α i := by
  intro j hj; have : j ≤ 3 := by omega
  interval_cases j <;> decide +kernel

lemma blk5_hB : ∀ j, j + 2 ≤ 5 → ∀ i c, |blk5M j i c| ≤ blk5B i c := by
  intro j hj; have : j ≤ 3 := by omega
  interval_cases j <;> decide +kernel

/-- Diagonal dominance of `U*_5`: `∑_{c ≠ i} max_j |M^{(j)}[i][c]| ≤ α_i ≤ a*_5 = 16`. -/
lemma blk5_dom : (∀ i, ∑ c ∈ univ.erase i, blk5B i c ≤ blk5α i) ∧ (∀ i, blk5α i ≤ ((16 : ℕ) : ℤ)) ∧
    ∀ i, ∑ c, blk5B i c ≤ 63 := by
  decide +kernel

lemma blk5_opts : blk5Opts = List.ofFn fun k => caOpts blk5M (Fin.rev k) := by decide +kernel

lemma blk5_st0 : blk5St0 = caStart 5 := by decide +kernel

/-- **`thm:block`(c), `s = 5`, proof range** (the written diagonal-dominance argument): for every prime
`p ≥ 5 a*_5 + 4 = 84` every step has a term `≥ 1 - 17/p`, i.e. `LB(F) ≥ 1 - 17/p`. -/
theorem blk5_LB_proof (hp : 84 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  have := dom_LB (p := p) (by norm_num) blk5F blk5M blk5_hM blk5α blk5B 16 blk5_diag
    (fun j hj i c _ => blk5_hB j hj i c) blk5_dom.1 blk5_dom.2.1 (by omega) K e l h
  convert this using 2; push_cast; ring

/-- The bound at one prime from one evaluation of the checker (`caCheck_sound`). -/
theorem blk5_LB_chk (hchk : caCheck 5 blk5Opts blk5St0 p 16 = true) (hp : 17 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  have := caCheck_sound (p := p) (by norm_num) blk5F blk5M blk5_hM blk5B blk5_hB blk5_dom.2.2 _ blk5_opts _
    blk5_st0 16 (by omega) hchk K e l h
  convert this using 2; push_cast; ring

end GeoSeq
