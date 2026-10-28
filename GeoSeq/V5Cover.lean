/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs
public import GeoSeq.V2WS

@[expose] public section

/-!
# GeoSeq stage V5: coverings of staggered columns (`lem:D`)

* **`cover_iff`**: condition (ii) of `prop:steer` for column `j` with arbitrary windows ⟺ for every `σ` some own
  value `o ∈ Wo^{(j)}` has `σ_c + o κ_{c←j} ∈ W_{c←j}` for every `c ≠ j` (the computation in the proof of
  `lem:lexcover`, which `sec:antipode` uses for the doubled columns).
* **`lemD`** (`lem:D`, doubling): if `v` represents `2u` and satisfies the hypotheses of `lem:ws`, then every
  run of `2N_k - 1` consecutive integers contains an `o` with `σ + o u ∈ I_1 × ⋯ × I_k`.
-/

namespace GeoSeq

open Finset

section Cover

variable {F : Type*} [Field F] {s : ℕ}

/-- **Condition (ii) for any windows** (the computation in the proof of `lem:lexcover`): every line
`β + 𝔽 α_j` meets `W^{(j)}` iff for every `σ` some `o ∈ Wo^{(j)}` has `σ_c + o κ_{c←j} ∈ W_{c←j}` (`c ≠ j`). -/
theorem cover_iff (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (W : Fin s → Fin s → Set F)
    (j : Fin s) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin W j) ↔
      ∀ σ : Fin s → F, ∃ o ∈ W j j, ∀ c, c ≠ j → σ c + o * kapL θ lamv zθ c j ∈ W c j := by
  constructor
  · intro h σ
    obtain ⟨t, ht⟩ := h (fun c => if c = j then 0 else σ c)
    refine ⟨t, ?_, fun c hc => ?_⟩
    · have := ht j
      simpa [stAlpha] using this
    · have := ht c
      simpa [stAlpha, hc, mul_comm] using this
  · intro h β
    obtain ⟨o, ho, hc⟩ := h (fun c => β c - β j * kapL θ lamv zθ c j)
    refine ⟨o - β j, fun c => ?_⟩
    by_cases hcj : c = j
    · subst hcj; simpa [stAlpha] using ho
    · have := hc c hcj
      simp only [Pi.add_apply, Pi.smul_apply, stAlpha, if_neg hcj, smul_eq_mul]
      convert this using 1; ring

end Cover

/-- **`lem:D`** (doubling): let `u ∈ 𝔽_p^k`, let `v ∈ ℤ^k` represent `2u`, and suppose `v` satisfies the
hypotheses of `lem:ws` for arcs `I_1, …, I_k` (rows indexed from `0`), with number `N_k`. Then every run
`a, a+1, …, a + 2N_k - 2` of `2N_k - 1` consecutive integers contains an `o` with `σ + o u ∈ I_1 × ⋯ × I_k`,
for every `σ`. -/
theorem lemD (p : ℕ) [NeZero p] (k : ℕ) (hk : 1 ≤ k) (u : ℕ → ZMod p) (v : ℕ → ℤ)
    (hv2 : ∀ t < k, (v t : ZMod p) = 2 * u t) (L : ℕ → ℤ) (len : ℕ → ℕ)
    (hlen : ∀ t < k, len t ≤ p) (hv : ∀ t < k, 1 ≤ (v t).natAbs) (h1 : (v 0).natAbs ≤ len 0)
    (hN : ∀ t, t + 1 < k →
      wsN p len (fun t => (v t).natAbs) t * (v (t + 1)).natAbs ≤ len (t + 1))
    (σ : ℕ → ZMod p) (a : ℤ) :
    ∃ o : ℤ, a ≤ o ∧ o ≤ a + 2 * ((wsN p len (fun t => (v t).natAbs) (k - 1) : ℤ) - 1) ∧
      ∀ t < k, σ t + (o : ZMod p) * u t ∈ arc p (L t) (len t) := by
  obtain ⟨o', h0, hlt, hgood⟩ := ws_cover p k hk v L len hlen hv h1 hN (fun t => σ t + (a : ZMod p) * u t) 0
  refine ⟨a + 2 * o', by omega, by omega, fun t ht => ?_⟩
  have := hgood t ht
  convert this using 1
  rw [hv2 t ht]; push_cast; ring

end GeoSeq
