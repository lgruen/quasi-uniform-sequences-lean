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
# GeoSeq stage V9-9 (part 2): `thm:block`(c) for `s = 4`

* `blk4a_injective`, `blk4v_ne`, `blk4_hrel` (identity (a) of `def:block`, every prime `p ≥ 5`, by evaluation at the
  places), `blk4_hNd` (vanishing orders), `blk4_hM` (partial sums), `blk4_dom` (diagonal dominance data).
* **`blk4_LB_proof`**: the written argument (diagonal dominance) for `p ≥ 5 a*_4 + 4 = 29`.
* `blk4_chk7`, …, `blk4_chk23` (kernel evaluation of `caCheck`, `decide +kernel`) and **`blk4_LB_ca`**: the
  computer-assisted range `7 ≤ p ≤ 23` (`tab:block`: the paper evaluates `LB(F)` at every prime `7 ≤ p ≤ 109`;
  `blk4_chk29`, …, `blk4_chk109` give the remaining primes of that range as well).
* **`blk4_block`** (`thm:block`(c), `s = 4`): for every prime `p ≥ 7` and `θ ≠ 0`, a digital `(0,4)`-sequence with the
  design relation at every `P_{16K}` and `sep(P_{16K}) ≥ 1 - 6/p`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

lemma blk4a_injective (hp : 5 ≤ p) : Function.Injective (blk4a (p := p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h21 : (2 : ZMod p) ≠ 1 := fun h => h1 (by linear_combination h)
  have h31 : (3 : ZMod p) ≠ 1 := fun h => h2 (by linear_combination h)
  have h32 : (3 : ZMod p) ≠ 2 := fun h => h1 (by linear_combination h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [blk4a] at h ⊢ <;> (try field_simp at h) <;>
    simp_all

lemma blk4v_ne (hp : 5 ≤ p) (c : Fin 4) : blk4v (p := p) c ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  fin_cases c <;> simp [blk4v, h2, h3]

set_option maxHeartbeats 1000000 in
lemma blk4_hev (hp : 5 ≤ p) : ∀ c i, i ≠ c → ∀ j, j ≠ c →
    (∏ i' : Fin 4, if i' = c ∨ i' = i then 1 else (blk4a (p := p) j - blk4a i')) =
      -(blk4v i) * ∑ n ∈ range (4 - 1), blockF blk4F n i c * ((blk4a j - blk4a c) ^ n *
        ∑ k ∈ range (4 - 1 - n), cfOf (s := 4) blk4cfL 6 c n k * blk4a j ^ k) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h6 : (6 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  intro c i hic j hjc
  fin_cases c <;> fin_cases i <;> fin_cases j <;> simp at hic hjc ⊢ <;>
    simp [Fin.prod_univ_four, Finset.sum_range_succ, blk4a, blk4v, blockF, blk4F, cfOf, blk4cfL] <;>
    field_simp <;> norm_num

/-- **Identity (a) of `def:block` for `thm:block`(c), `s = 4`**, for every prime `p ≥ 5`. -/
theorem blk4_hrel (hp : 5 ≤ p) (c i : Fin 4) (h : i ≠ c) :
    wCoCo (blk4a (p := p)) c i = -C (blk4v i) *
      ∑ n ∈ range (4 - 1), C (blockF blk4F n i c) * blk4N c (4 - 1 - n) :=
  hrel_of_eval (by norm_num) _ (blk4a_injective hp) _ _ _ (blk4_hev hp) c i h

/-- The vanishing orders of the design numerators of `thm:block`(c), `s = 4` (every prime `p ≥ 5`). -/
theorem blk4_hNd (hp : 5 ≤ p) (c : Fin 4) (n : ℕ) (hn : n + 2 ≤ 4) :
    ∃ N', blk4N (p := p) c (4 - 1 - n) = (X - C (blk4a c)) ^ n * N' ∧ N'.eval (blk4a c) ≠ 0 := by
  refine hNd_of_ndPoly _ _ (fun c n hn => ?_) c n hn
  have h2 : (2 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h6 : (6 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have h27 : (27 : ZMod p) ≠ 0 := zmod_ofNat_ne hp _ (by norm_num)
  have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl | rfl <;> fin_cases c <;>
    simp [Finset.sum_range_succ, blk4a, cfOf, blk4cfL] <;> (try field_simp) <;> (try norm_num) <;> smooth_ne hp

/-! ## The bound -/

/-- The diagonal `α = (5, 3, 5, 3)` of `U*_4` (`F_0[c][c] = -α_c`, zero deeper diagonal). -/
def blk4α : Fin 4 → ℤ := ![5, 3, 5, 3]

/-- The bounds `B_{ic} = max_j |M^{(j)}[i][c]|` of `U*_4` (diagonal `α`). -/
def blk4B : Fin 4 → Fin 4 → ℤ := !![5, 2, 1, 2; 1, 3, 1, 1; 1, 2, 5, 2; 1, 1, 1, 3]

lemma blk4_hM : ∀ j, j + 2 ≤ 4 → ∀ i c, blk4M j i c = ∑ n ∈ range (j + 1), blk4F n i c := by
  intro j hj; have : j ≤ 2 := by omega
  interval_cases j <;> decide +kernel

lemma blk4_diag : ∀ j, j + 2 ≤ 4 → ∀ i, blk4M j i i = -blk4α i := by
  intro j hj; have : j ≤ 2 := by omega
  interval_cases j <;> decide +kernel

lemma blk4_hB : ∀ j, j + 2 ≤ 4 → ∀ i c, |blk4M j i c| ≤ blk4B i c := by
  intro j hj; have : j ≤ 2 := by omega
  interval_cases j <;> decide +kernel

/-- Diagonal dominance of `U*_4`: `∑_{c ≠ i} max_j |M^{(j)}[i][c]| ≤ α_i ≤ a*_4 = 5`. -/
lemma blk4_dom : (∀ i, ∑ c ∈ univ.erase i, blk4B i c ≤ blk4α i) ∧ (∀ i, blk4α i ≤ ((5 : ℕ) : ℤ)) ∧
    ∀ i, ∑ c, blk4B i c ≤ 63 := by
  decide +kernel

lemma blk4_opts : blk4Opts = List.ofFn fun k => caOpts blk4M (Fin.rev k) := by decide +kernel

lemma blk4_st0 : blk4St0 = caStart 4 := by decide +kernel

/-- **`thm:block`(c), `s = 4`, proof range** (the written diagonal-dominance argument): for every prime
`p ≥ 5 a*_4 + 4 = 29` every step has a term `≥ 1 - 6/p`, i.e. `LB(F) ≥ 1 - 6/p`. -/
theorem blk4_LB_proof (hp : 29 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  have := dom_LB (p := p) (by norm_num) blk4F blk4M blk4_hM blk4α blk4B 5 blk4_diag
    (fun j hj i c _ => blk4_hB j hj i c) blk4_dom.1 blk4_dom.2.1 (by omega) K e l h
  convert this using 2; push_cast; ring

/-- The bound at one prime from one evaluation of the checker (`caCheck_sound`). -/
theorem blk4_LB_chk (hchk : caCheck 4 blk4Opts blk4St0 p 5 = true) (hp : 6 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  intro e l h
  have := caCheck_sound (p := p) (by norm_num) blk4F blk4M blk4_hM blk4B blk4_hB blk4_dom.2.2 _ blk4_opts _
    blk4_st0 5 (by omega) hchk K e l h
  convert this using 2; push_cast; ring

/-! Kernel evaluations of the one-digit relaxation (`thm:block`(c), "Small primes"; `tab:block`, c.a. column). -/

theorem blk4_chk7 : caCheck 4 blk4Opts blk4St0 7 5 = true := by decide +kernel
theorem blk4_chk11 : caCheck 4 blk4Opts blk4St0 11 5 = true := by decide +kernel
theorem blk4_chk13 : caCheck 4 blk4Opts blk4St0 13 5 = true := by decide +kernel
theorem blk4_chk17 : caCheck 4 blk4Opts blk4St0 17 5 = true := by decide +kernel
theorem blk4_chk19 : caCheck 4 blk4Opts blk4St0 19 5 = true := by decide +kernel
theorem blk4_chk23 : caCheck 4 blk4Opts blk4St0 23 5 = true := by decide +kernel

/-- **`thm:block`(c), `s = 4`, computer-assisted range below the proof range**: `LB(F) ≥ 1 - 6/p` at every prime
`7 ≤ p < 29`, i.e. `p = 7, 11, 13, 17, 19, 23` (kernel evaluation of `caCheck`, one per prime). -/
theorem blk4_LB_ca (hp7 : 7 ≤ p) (hp : p < 29) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  refine blk4_LB_chk ?_ (by omega) K
  have hpr := (Fact.out : p.Prime)
  interval_cases p <;> first
    | (exfalso; norm_num at hpr; done)
    | with_reducible exact blk4_chk7 | with_reducible exact blk4_chk11 | with_reducible exact blk4_chk13
    | with_reducible exact blk4_chk17 | with_reducible exact blk4_chk19 | with_reducible exact blk4_chk23

/-! The remaining primes of the computer-assisted range `7 ≤ p ≤ 109` of `tab:block` (not needed for `blk4_block`,
which uses the written argument from `p = 29` on). -/

theorem blk4_chk29 : caCheck 4 blk4Opts blk4St0 29 5 = true := by decide +kernel
theorem blk4_chk31 : caCheck 4 blk4Opts blk4St0 31 5 = true := by decide +kernel
theorem blk4_chk37 : caCheck 4 blk4Opts blk4St0 37 5 = true := by decide +kernel
theorem blk4_chk41 : caCheck 4 blk4Opts blk4St0 41 5 = true := by decide +kernel
theorem blk4_chk43 : caCheck 4 blk4Opts blk4St0 43 5 = true := by decide +kernel
theorem blk4_chk47 : caCheck 4 blk4Opts blk4St0 47 5 = true := by decide +kernel
theorem blk4_chk53 : caCheck 4 blk4Opts blk4St0 53 5 = true := by decide +kernel
theorem blk4_chk59 : caCheck 4 blk4Opts blk4St0 59 5 = true := by decide +kernel
theorem blk4_chk61 : caCheck 4 blk4Opts blk4St0 61 5 = true := by decide +kernel
theorem blk4_chk67 : caCheck 4 blk4Opts blk4St0 67 5 = true := by decide +kernel
theorem blk4_chk71 : caCheck 4 blk4Opts blk4St0 71 5 = true := by decide +kernel
theorem blk4_chk73 : caCheck 4 blk4Opts blk4St0 73 5 = true := by decide +kernel
theorem blk4_chk79 : caCheck 4 blk4Opts blk4St0 79 5 = true := by decide +kernel
theorem blk4_chk83 : caCheck 4 blk4Opts blk4St0 83 5 = true := by decide +kernel
theorem blk4_chk89 : caCheck 4 blk4Opts blk4St0 89 5 = true := by decide +kernel
theorem blk4_chk97 : caCheck 4 blk4Opts blk4St0 97 5 = true := by decide +kernel
theorem blk4_chk101 : caCheck 4 blk4Opts blk4St0 101 5 = true := by decide +kernel
theorem blk4_chk103 : caCheck 4 blk4Opts blk4St0 103 5 = true := by decide +kernel
theorem blk4_chk107 : caCheck 4 blk4Opts blk4St0 107 5 = true := by decide +kernel
theorem blk4_chk109 : caCheck 4 blk4Opts blk4St0 109 5 = true := by decide +kernel

/-- **`thm:block`(c), `s = 4`, the full computer-assisted range of `tab:block`**: `LB(F) ≥ 1 - 6/p` at every prime
`7 ≤ p ≤ 109` by kernel evaluation (independently of the written argument). -/
theorem blk4_LB_ca109 (hp7 : 7 ≤ p) (hp : p ≤ 109) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) := by
  refine blk4_LB_chk ?_ (by omega) K
  have hpr := (Fact.out : p.Prime)
  interval_cases p <;> first
    | (exfalso; norm_num at hpr; done)
    | with_reducible exact blk4_chk7 | with_reducible exact blk4_chk11 | with_reducible exact blk4_chk13
    | with_reducible exact blk4_chk17 | with_reducible exact blk4_chk19 | with_reducible exact blk4_chk23
    | with_reducible exact blk4_chk29 | with_reducible exact blk4_chk31 | with_reducible exact blk4_chk37
    | with_reducible exact blk4_chk41 | with_reducible exact blk4_chk43 | with_reducible exact blk4_chk47
    | with_reducible exact blk4_chk53 | with_reducible exact blk4_chk59 | with_reducible exact blk4_chk61
    | with_reducible exact blk4_chk67 | with_reducible exact blk4_chk71 | with_reducible exact blk4_chk73
    | with_reducible exact blk4_chk79 | with_reducible exact blk4_chk83 | with_reducible exact blk4_chk89
    | with_reducible exact blk4_chk97 | with_reducible exact blk4_chk101 | with_reducible exact blk4_chk103
    | with_reducible exact blk4_chk107 | with_reducible exact blk4_chk109

/-- **`thm:block`(c), `s = 4`**: places `(0, 1, 1/2, 1/3)`, `v = (1, 1, 2, 3)`, the design `U*_4` (`tab:block`). For
every prime `p ≥ 7` and `θ ≠ 0` the sequence is a digital `(0,4)`-sequence, at every full level `P_{16K}` the geometric
digits follow the design exactly, and `sep(P_{16K}) ≥ 1 - 6/p` for every `K ≥ 1` (`p ≥ 29`: the written argument
`blk4_LB_proof`; `7 ≤ p ≤ 23`: the kernel evaluations `blk4_LB_ca`). -/
theorem blk4_block (hp : 7 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk4 θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (4 * (4 * K)) →
        seqDigit (zcode p) (blk4 θ) x i (4 * K) =
          ∑ c, ∑ n ∈ range (4 - 1), blockF blk4F n i c * seqDigit (zcode p) (blk4 θ) x c (4 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 4 (4 * K) (seqPoint (zcode p) (blk4 θ)) (((p : ℝ) - 6) / p) := by
  have ha := blk4a_injective (p := p) (by omega)
  have hv := blk4v_ne (p := p) (by omega)
  have hv1 : ∀ c, (1 : Fin 4 → ZMod p) c ≠ 0 := fun c => one_ne_zero
  have hNd := blk4_hNd (p := p) (by omega)
  have hrel := blk4_hrel (p := p) (by omega)
  refine ⟨blockGen_t0 θ 4 blk4v _ blk4N 1 (zcode p) ha hθ le_rfl (by norm_num) hv hv1 hNd,
    fun K hK i x hx => blockGen_rel_seq blk4a θ 4 blk4v _ blk4N 1 (zcode p) ha hθ le_rfl (by norm_num)
      hrel hv K hK i x hx, fun K hK => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hLB1 : ((p : ℝ) - 6) / p ≤ 1 := by rw [div_le_one hp0]; linarith
  have h := block_sep blk4a ha θ hθ 4 le_rfl (by norm_num) blk4v hv (blockF blk4F) blk4N 1 hv1 hNd hrel K hK
    (((p : ℝ) - 6) / p) ?_
  · rwa [min_eq_right hLB1] at h
  by_cases h29 : 29 ≤ p
  · exact blk4_LB_proof h29 (4 * K)
  · exact blk4_LB_ca hp (by omega) (4 * K)

end GeoSeq
