/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Inst

@[expose] public section

/-!
# GeoSeq stage V9-6 (part 5): `thm:blocktwo`, `prop:implied` (separation forms), `rem:prefixcases` (`s²ℕ`)

* **`blocktwo`** (`thm:blocktwo`): with block period `ℓ ≥ s` and a second check vector `v'`: (i) `(0,s)`; (ii) the design
  relation at every design level `ℓK` and `sep(P_{sℓK}) ≥ min(1, LB)`; (iii) at every skeleton level `m = s(T+1) - 1`,
  `T ≡ 1, …, ℓ - s (mod ℓ)`, the skeleton relation with `v'` and `sep(P_{s(T+1)-1}) ≥ p^{-1/s} ℓ_jit(Λ_{v'})`.
* **`implied_sep`** (`prop:implied`, last sentence): `sep(P_{s(ℓK+1)-1}) ≥ p^{-1/s} ℓ_jit(Λ_{v̄})` for every `K ≥ 0`.
* `hasGap_s2N` (`rem:prefixcases`, the family `s²ℕ`): largest gap `s²`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

lemma seqDigit_blockDig (a : Fin s → ZMod p) (θ : ZMod p) (ℓ : ℕ) (v : Fin s → ZMod p)
    (Fd : ℕ → Fin s → Fin s → ZMod p) (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (M x : ℕ)
    (hx : x < p ^ M) (c : Fin s) (d : ℕ) :
    seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x c d =
      blockDig a θ ℓ v Fd Nd v' c d (vecPoly (fun j => idxDigit (zcode p) x j) M) := by
  rw [seqDigit_eq_range (zcode p) _ x c _ _ fun j hj => idxDigit_eq_zero (zcode p) x j
    (digit_high x j (lt_of_lt_of_le hx (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hj))), blockGen_vecPoly]

/-- **`thm:blocktwo`**: a block-periodic residue sequence with block period `ℓ ≥ s`, row constants `v`, design `F`
(numerators satisfying (a) and the orders), second check vector `v'`: (i) a digital `(0,s)`-sequence; (ii) at every
design level the design relation holds and `sep(P_{sℓK}) ≥ min(1, LB)`; (iii) at every skeleton level
`m = s(T+1) - 1`, `T = ℓn + j`, `1 ≤ j ≤ ℓ - s`, the skeleton relation with `v'` holds and
`sep(P_{s(T+1)-1}) ≥ p^{-1/s} ℓ_jit(Λ_{v'})`. -/
theorem blocktwo (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n)) :
    IsSeq0 (zcode p) (blockGen a θ ℓ v Fd Nd v') ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (s * (ℓ * K)) →
        seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) =
          ∑ c, ∑ n ∈ range (s - 1), Fd n i c * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x c (ℓ * K - 1 - n)) ∧
      (∀ K, 1 ≤ K → ∀ LB : ℝ, (∀ e l, IsStep (ℓ * K) e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
          (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), Fd n i c') : ℝ) / p) ^ 2)) →
        SepAtLevel p s (ℓ * K) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v')) (min 1 LB)) ∧
      (∀ n j, 1 ≤ j → j + s ≤ ℓ →
        (∀ x, x < p ^ (s * (ℓ * n + j + 1) - 1) →
          ∑ c, v' c * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x c (ℓ * n + j) = 0) ∧
        SepAtPrefix p s (s * (ℓ * n + j + 1) - 1) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v'))
          ((p : ℝ) ^ (-(1 / (s : ℝ))) * ljit v')) := by
  have hs : 1 ≤ s := by omega
  have hseq := blockGen_t0 θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hv hv' hNd
  refine ⟨hseq, fun K hK i x hx => blockGen_rel_seq a θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hrel hv K hK i x hx,
    fun K hK LB hLB => block_sep a ha θ hθ ℓ hsℓ hs2 v hv Fd Nd v' hv' hNd hrel K hK LB hLB,
    fun n j hj1 hj => ?_⟩
  have hsk : ∀ x, x < p ^ (s * (ℓ * n + j + 1) - 1) →
      ∑ c, v' c * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x c (ℓ * n + j) = 0 := by
    intro x hx
    simp_rw [seqDigit_blockDig a θ ℓ v Fd Nd v' _ x hx]
    have h2 : 2 ≤ s * (ℓ * n + j + 1) := le_trans hs2 (Nat.le_mul_of_pos_right _ (by omega))
    exact blockGen_skel a θ ℓ v Fd Nd v' ha hv' n j hj1 hj hs _ _ (by omega)
  refine ⟨hsk, ?_⟩
  have := skel_sepAtPrefix hs2 _ hseq v' (ljit v') (fun b hb hlat => ljit_le v' b hb hlat) (ℓ * n + j + 1)
    (by omega) (by simpa using hsk)
  exact this

/-- **`prop:implied`** (separation): under the hypotheses of `blockGen_implied`, the skeleton relation with `v̄` holds on
`P_{s(ℓK+1)-1}` and `sep(P_{s(ℓK+1)-1}) ≥ p^{-1/s} ℓ_jit(Λ_{v̄})` for every `K ≥ 0`. -/
theorem implied_sep (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (ℓ : ℕ)
    (hsℓ : s ≤ ℓ) (hs2 : 2 ≤ s) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → ZMod p)
    (Nd : Fin s → ℕ → (ZMod p)[X]) (v' : Fin s → ZMod p) (hv' : ∀ c, v' c ≠ 0)
    (hNd : ∀ c n, n + 2 ≤ s → ∃ N', Nd c (ℓ - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0)
    (hrel : ∀ c i, i ≠ c →
      wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * Nd c (ℓ - 1 - n))
    (vb : Fin s → ZMod p) (ξ : ZMod p) (hvb : ∀ i, vb i = ξ * v i / (wCo a i).eval (a i))
    (hF : ∀ n c, n + 2 ≤ s → ∑ i, vb i * Fd n i c = 0) (K : ℕ) :
    (∀ x, x < p ^ (s * (ℓ * K + 1) - 1) →
        ∑ i, vb i * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) = 0) ∧
      SepAtPrefix p s (s * (ℓ * K + 1) - 1) (seqPoint (zcode p) (blockGen a θ ℓ v Fd Nd v'))
        ((p : ℝ) ^ (-(1 / (s : ℝ))) * ljit vb) := by
  have hs : 1 ≤ s := by omega
  have hseq := blockGen_t0 θ ℓ v Fd Nd v' (zcode p) ha hθ hsℓ hs hv hv' hNd
  have hsk : ∀ x, x < p ^ (s * (ℓ * K + 1) - 1) →
      ∑ i, vb i * seqDigit (zcode p) (blockGen a θ ℓ v Fd Nd v') x i (ℓ * K) = 0 := by
    intro x hx
    simp_rw [seqDigit_blockDig a θ ℓ v Fd Nd v' _ x hx]
    have h2 : 2 ≤ s * (ℓ * K + 1) := le_trans hs2 (Nat.le_mul_of_pos_right _ (by omega))
    exact blockGen_implied a θ ℓ v Fd Nd v' ha hθ hsℓ hs2 hrel hv vb ξ hvb hF K _ _ (by omega)
  refine ⟨hsk, ?_⟩
  exact skel_sepAtPrefix hs2 _ hseq vb (ljit vb) (fun b hb hlat => ljit_le vb b hb hlat) (ℓ * K + 1)
    (by omega) (by simpa using hsk)

/-- `rem:prefixcases`, the family `s²ℕ`: every `m` has an element `s²K'` (`K' ≥ 1`) with `m < s²K' ≤ m + s²`. -/
lemma hasGap_s2N (hs : 1 ≤ s) : HasGap (fun m => ∃ K, 1 ≤ K ∧ m = s ^ 2 * K) (s ^ 2) := by
  intro m
  have hs2 : 0 < s ^ 2 := by positivity
  refine ⟨s ^ 2 * (m / s ^ 2 + 1), ⟨m / s ^ 2 + 1, Nat.le_add_left 1 _, rfl⟩, ?_, ?_⟩
  · have := Nat.lt_mul_div_succ m hs2; linarith
  · have := Nat.mul_div_le m (s ^ 2); rw [mul_add, mul_one]; linarith

end GeoSeq
