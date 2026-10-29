/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V9Thm
public import GeoSeq.N1

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 6): leftovers — `rem:residuefull`, `cor:N1` (offset-map phrasing)

* **`residue_full`** (`rem:residuefull`, the inclusion bound): `P_{sK} ⊂ P_{s(K+1)-1}` and `thm:residue` give
  `sep(P_{sK}) ≥ ℓ_jit(Λ_v)/p` for the residue sequence, at every full level (also `K = 0`).
* **`N1_offset`** (`cor:N1`, "in particular"): no scramble of the frame `(0, 1)` over a finite field has an offset map
  that depends only on the finest cell digits (all carry responses finest-digit, `LawFinest`) at two consecutive
  levels `K, K + 1 ≥ 2`.
-/

namespace GeoSeq

open Finset Polynomial

section Full
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`rem:residuefull`** (inclusion bound): for the residue sequence (`s ≥ 2`, distinct places, `θ ≠ 0`, `v_c ≠ 0`),
every full level satisfies `sep(P_{sK}) ≥ ℓ_jit(Λ_v)/p`: any two distinct points of `P_{sK}` have toroidal distance
`≥ ℓ_jit(Λ_v) p^{-(K+1)}`. -/
theorem residue_full (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0)
    (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) :
    SepAtLevel p s K (seqPoint (zcode p) (resSeq a θ v)) (ljit v / p) := by
  intro x y hx hy hxy
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hle : p ^ (s * K) ≤ p ^ (s * (K + 1) - 1) := Nat.pow_le_pow_right hp (by rw [Nat.mul_succ]; omega)
  have h := residue_sep_ljit hs a ha θ hθ v hv (K + 1) (by omega) x y (hx.trans_le hle) (hy.trans_le hle) hxy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hp0, pow_succ] at *
  linarith

end Full

section Offset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`cor:N1`, offset-map phrasing** ("in particular"): for the frame `a_0 = 0`, `a_1 = 1` and any scramble
`(L_0, L_1)` (nonzero diagonal) over a finite field, the offset map is not finest-digit (every carry response
`D(l)[c][c']`, `1 ≤ l ≤ K`, independent of `l`: a sheared lattice without jumps) at two consecutive levels
`K, K + 1 ≥ 2`. -/
theorem N1_offset (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (K : ℕ) (hK : 2 ≤ K) :
    ¬ ((∀ c c', LawFinest (scrGen ![0, 1] L) K c c') ∧ ∀ c c', LawFinest (scrGen ![0, 1] L) (K + 1) c c') :=
  fun ⟨h1, h2⟩ => N1 L hL K hK ⟨h1 0 1, h2 0 1, h1 1 1⟩

end Offset

end GeoSeq
