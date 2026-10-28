/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# Statements: the brick wall (`sec:WF`), GeoSeq stage S0

* `thm:WF`: `WF_net` (`t = 0`; PROVED in stage S1, `GeoSeq/FrameNets.lean`), `WF_sep`
  (`c(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`; PROVED in stage S3, `GeoSeq/WFLaw.lean`).
* `thm:WF`, quasi-uniform clause (earlier `cor:WF`): `WF_allN` (`δ(P_{[N]}) ≥ (p-3)/(2p²) N^{-1/2}`; PROVED in stage S3), `WF_mesh`
  (`h ≤ 2√2 p²/(p-3) · δ`; PROVED in stage S5, `GeoSeq/Mesh.lean`, via the covering half of
  `lem:prefix`).
* `lem:WFlaw`, coordinate `1`: `WF_law_O1` (`O_1^{(l)} = 0`), `WF_law_X10`
  (`X_{1←0}^{(l)} = ½(∓1)^l`, i.e. `½ (-a)^l` for `ρ = √(1 + a x)`). PROVED in stage S3
  (`GeoSeq/WFLaw.lean`, via `prop:law` and `lem:gform`).
* The arithmetic core of the proof of `thm:WF`: `WF_coord1`, `WF_LB1` (every prime `p ≥ 5`) and
  `WF_coord1_p7` (kernel `decide`). PROVED (`GeoSeq/OneDigit.lean`).

`a = -1` is the brick wall `W^-`, `a = 1` its companion `W^+`.

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:WFlaw`** (own response of coordinate `1`): for `W^±`, every level `K` and carry length
`1 ≤ l ≤ K`, `O_1^{(l)} = D(l)[1][1] = 0`. -/
theorem WF_law_O1 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    IsCarryEntry (WFgen p a) K 0 l 1 1 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:WFlaw`** (cross response into coordinate `1`): for `W^±`, every level `K` and carry
length `1 ≤ l ≤ K`, `X_{1←0}^{(l)} = D(l)[1][0] = ½ (∓1)^l` (`= ½ (-a)^l`). -/
theorem WF_law_X10 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    IsCarryEntry (WFgen p a) K 0 l 1 0 ((2 : ZMod p)⁻¹ * (-a) ^ l) := by
  sorry

/-- **`thm:WF`** (`t = 0`; V3 states `W^-`, i.e. `a = -1`; Lean: both signs): both brick walls are `(0,2)`-sequences in base `p ≥ 5`. -/
theorem WF_net (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1) :
    IsSeq0 (zcode p) (WFgen p a) := by
  sorry

/-- **`thm:WF`** (separation): `c(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`. -/
theorem WF_sep (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p)) := by
  sorry

/-- **`thm:WF`, quasi-uniform clause** (earlier `cor:WF`; separation along all `N`): `δ(P_{[N]}) ≥ (p-3)/(2p²) · N^{-1/2}` for `N ≥ 2`. -/
theorem WF_allN (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1) :
    SepAllN 2 (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p ^ 2)) := by
  sorry

/-- **`thm:WF`, quasi-uniform clause** (earlier `cor:WF`; mesh ratio along all `N`): `h(P_{[N]}) ≤ 2√2 p²/(p-3) · δ(P_{[N]})`, with `h` the
Euclidean covering radius and `δ = 2 · sepRad` the toroidal separation. -/
theorem WF_mesh (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (WFgen p a))) ≤
      2 * Real.sqrt 2 * (p : ℝ) ^ 2 / ((p : ℝ) - 3) *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (WFgen p a)))) := by
  sorry

/-- **`thm:WF`, arithmetic core** (coordinate `1`, one geometric digit): with `O_1^{(l)} = 0` and
`X_{1←0}^{(l)} = x ∈ {1/2, -1/2}`, every step `e ∈ {-1,0,1}² ∖ {0}` has
`f_1(e_1, e_0 x) ≥ (p-3)/(2p)` (numerators: `p - 3 ≤ 2 · gapNum1`). -/
theorem WF_coord1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (e0 e1 : ℤ)
    (he0 : e0 = -1 ∨ e0 = 0 ∨ e0 = 1) (he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1)
    (hne : e0 ≠ 0 ∨ e1 ≠ 0) (x : ZMod p)
    (hx : x = (2 : ZMod p)⁻¹ ∨ x = -(2 : ZMod p)⁻¹) :
    p - 3 ≤ 2 * gapNum1 p e1 ((e0 : ZMod p) * x) := by
  sorry

/-- **`thm:WF`, the certificate term** (`lem:cert`, `j = 1`, `s = 2`): for any change `σ_0` of the
geometric digit of coordinate `0`, `((p-3)/(2p))² ≤ f_1(e_0, σ_0)² + f_1(e_1, σ_1)²` (numerators). -/
theorem WF_LB1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (e0 e1 : ℤ)
    (he0 : e0 = -1 ∨ e0 = 0 ∨ e0 = 1) (he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1)
    (hne : e0 ≠ 0 ∨ e1 ≠ 0) (x : ZMod p)
    (hx : x = (2 : ZMod p)⁻¹ ∨ x = -(2 : ZMod p)⁻¹) (σ0 : ZMod p) :
    (p - 3) ^ 2 ≤ 4 * (gapNum1 p e0 σ0 ^ 2 + gapNum1 p e1 ((e0 : ZMod p) * x) ^ 2) := by
  sorry

/-- `WF_coord1` at `p = 7` (`1/2 = 4`, `-1/2 = 3`), an independent finite check. -/
theorem WF_coord1_p7 :
    ∀ e0 ∈ ({-1, 0, 1} : Finset ℤ), ∀ e1 ∈ ({-1, 0, 1} : Finset ℤ), (e0 ≠ 0 ∨ e1 ≠ 0) →
      ∀ x ∈ ({4, 3} : Finset (ZMod 7)), 4 ≤ 2 * gapNum1 7 e1 ((e0 : ZMod 7) * x) := by
  sorry

end GeoSeq
