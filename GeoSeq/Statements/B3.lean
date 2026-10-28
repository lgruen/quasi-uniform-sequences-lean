/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs
public import GeoSeq.B3Defs
public import GeoSeq.B3Data

@[expose] public section

/-!
# Statements: base three (`thm:B3`, `lem:frames`(b), `prop:automaton` for `thm:B3`, `cor:allprimes`),
GeoSeq stage S6

All PROVED (`GeoSeq/B3Auto.lean`, `GeoSeq/B3Law.lean`, `GeoSeq/B3Cert.lean`; generated verbatim from the
proof files' signatures). `B3_frames` (`τ^{-1} = ∏(1+x^{3^i})`, Mahler equation, digit rule),
`cartier_step`, `reach_A`, `reach_B` (the automaton in certificate form), `B3_frame_inv`, `B3_law`, `B3_net`,
`B3_faure`, `B3_ghat`, `B3_M`, `esem_init`, `B3_init` (law, `t = 0`, closed forms, initial states), the
`decide` checks `b3_*`, `resp_of_cert`, `B3_resp`, `B3_resp_occurs`, `B3_resp_card` (exact response sets per
source coordinate: `24` and `36` columns), `B3_cert_min` (`37865 = 91² + 172²`, attained at `e = (1,-1)`,
`l = (1,9)`), `B3_sep_one`, `B3_sep` (`c(P_{2K}) ≥ √37865/729 = 0.2669…`), `B3_allN` (`δ ≥ 0.0889 N^{-1/2}`),
`B3_mesh` (`h ≤ 16 δ`), `allprimes`, `allprimes_qu` (`cor:allprimes`).

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`lem:frames`(b) for `q = 3`**: the Kummer root `T3 = ∏_{i≥0}(1 + x^{3^i})` is `τ^{-1}`
(`τ = √(1+x)`), it satisfies the Mahler equation `T3(x) = (1 + x) T3(x³)`, and `[x^n] T3 = 1` exactly
when every base-3 digit of `n` is `0` or `1` (`0` otherwise). -/
theorem B3_frames : tau3 * T3 = 1 ∧ T3 = (1 + X) * expand 3 three_ne_zero T3 ∧
    ∀ n, coeff n T3 = if ∀ d ∈ Nat.digits 3 n, d ≤ 1 then 1 else 0 := by
  sorry

/-- **The Cartier step** (`prop:automaton`, proof): for `r < 3`, coefficient `3n + r` of a state is
coefficient `n` of `stepP r` of it. -/
theorem cartier_step (S : St3) (n r : ℕ) (hr : r < 3) :
    coeff (3 * n + r + 8) (esem S) = coeff (n + 8) (esem (stepP r S)) := by
  sorry

/-- **Closure ⟹ reachability** (states after a nonzero digit): if the list `A` of vectors is closed
under the three steps (with the transition table `tbl`), then every coefficient of a member of `A` is
the readout of a member of `A`. -/
theorem reach_A (A : List (List St3)) (tbl : List (List ℕ)) (N : ℕ) (hN : A.length = N)
    (h : ∀ s : Fin N, ∀ r : Fin 3, (tbl.getD s []).getD r 0 < N ∧
      stepV r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ vals (A.getD s []) n = vals (A.getD s' []) 0 := by
  sorry

/-- **Closure ⟹ reachability** (states before the first nonzero digit): with `B` closed under the
digit `0` and mapped into `A` by the digits `1, 2`, every coefficient `n ≥ 1` of a member of `B` is the
readout of a member of `A`. -/
theorem reach_B (A B : List (List St3)) (tA tB : List (List ℕ)) (N M : ℕ) (hN : A.length = N)
    (hM : B.length = M)
    (hA : ∀ s : Fin N, ∀ r : Fin 3, (tA.getD s []).getD r 0 < N ∧
      stepV r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepV 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepV r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ vals (B.getD s []) n = vals (A.getD s' []) 0 := by
  sorry

/-- **`thm:B3`**: `M G = 1` for the frame matrix `M = ((g_0, g_0 z_0), (g_1, g_1 z_1))` and
`G = B3G` (the Faure form of the earlier `lem:gform`). -/
theorem B3_frame_inv : frameM B3g B3z * B3G = 1 := by
  sorry

/-- **`thm:B3`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the base-3 sequence is `lawD B3g B3z B3G i l c c'` (independent of `K`). -/
theorem B3_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 2) :
    IsCarryEntry B3gen K i l c c' (lawD B3g B3z B3G i l c c') := by
  sorry

/-- **`thm:B3`** (`t = 0`): the base-3 sequence is a `(0,2)`-sequence. -/
theorem B3_net : IsSeq0 (zcode 3) B3gen := by
  sorry

/-- **`thm:B3`**: the sequence is a scramble `(L_0 P_0, L_1 P_1)` of the Faure sequence in base `3`
(`C_c = L_c P_{a_c}`, places `a_0 = 0`, `a_1 = 1`, `L_c[n][i] = [x^n] g_c (z_c - a_c)^i`). -/
theorem B3_faure : B3gen = scrGen ![0, 1] (ssScr B3g B3z) := by
  sorry

/-- **`thm:B3`, `Ĝ` in closed form**: `x² Q_p Ĝ[b][c'] = A + B τ^{-1}` with the numerators `B3An`. -/
theorem B3_ghat (b c' : Fin 2) :
    lps (B3An b c').1 + lps (B3An b c').2 * T3 = X ^ 2 * lps Qp3 * (B3G b c' * PowerSeries.mk 1) := by
  sorry

/-- **`thm:B3`, the frame matrix in closed form**: `M[c][b] = (P_0 + P_1 τ^{-1})/Q_p` with the
numerators `B3Mn`. -/
theorem B3_M (c b : Fin 2) : frameM B3g B3z c b = esem (B3Mn c b) := by
  sorry

/-- **The initial states** (`prop:automaton`, proof): `esem (initS i c c') = x^{8-i} F_i[c][c']`. -/
theorem esem_init (i : ℕ) (hi : i < 6) (c c' : Fin 2) :
    esem (initS i c c') = X ^ (8 - i) * B3F i c c' := by
  sorry

/-- **The initial states read the responses**: coefficient `l` of the initial state of entry
`(c, c')`, depth `i < 6`, is the carry response `D_i(l)[c][c']` of `prop:law`. -/
theorem B3_init (i : ℕ) (hi : i < 6) (c c' : Fin 2) (l : ℕ) :
    coeff (l + 8) (esem (initS i c c')) = lawD B3g B3z B3G i l c c' := by
  sorry

theorem b3_init0 : B3B0.getD 0 [] = initV 0 := by
  sorry

theorem b3_closeA0 : ∀ s : Fin 34, ∀ r : Fin 3, (B3tA0.getD s []).getD r 0 < 34 ∧
    stepV r (B3A0.getD s []) = B3A0.getD ((B3tA0.getD s []).getD r 0) [] := by
  sorry

theorem b3_closeB0 : ∀ s : Fin 3, ((B3tB0.getD s []).getD 0 0 < 3 ∧
    stepV 0 (B3B0.getD s []) = B3B0.getD ((B3tB0.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 3, r ≠ 0 → (B3tB0.getD s []).getD r 0 < 34 ∧
      stepV r (B3B0.getD s []) = B3A0.getD ((B3tB0.getD s []).getD r 0) [] := by
  sorry

theorem b3_read0 : ∀ s : Fin 34, B3out0.getD s 0 < 24 ∧
    (B3A0.getD s []).map acoef = B3tup0.getD (B3out0.getD s 0) [] := by
  sorry

theorem b3_wit0 : ∀ t : Fin 24, (∀ d ∈ B3wit0.getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 (B3wit0.getD t []) ∧
    (readV (B3wit0.getD t []) (initV 0)).map acoef = B3tup0.getD t [] := by
  sorry

theorem b3_init1 : B3B1.getD 0 [] = initV 1 := by
  sorry

theorem b3_closeA1 : ∀ s : Fin 87, ∀ r : Fin 3, (B3tA1.getD s []).getD r 0 < 87 ∧
    stepV r (B3A1.getD s []) = B3A1.getD ((B3tA1.getD s []).getD r 0) [] := by
  sorry

theorem b3_closeB1 : ∀ s : Fin 4, ((B3tB1.getD s []).getD 0 0 < 4 ∧
    stepV 0 (B3B1.getD s []) = B3B1.getD ((B3tB1.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 3, r ≠ 0 → (B3tB1.getD s []).getD r 0 < 87 ∧
      stepV r (B3B1.getD s []) = B3A1.getD ((B3tB1.getD s []).getD r 0) [] := by
  sorry

theorem b3_read1 : ∀ s : Fin 87, B3out1.getD s 0 < 36 ∧
    (B3A1.getD s []).map acoef = B3tup1.getD (B3out1.getD s 0) [] := by
  sorry

theorem b3_wit1 : ∀ t : Fin 36, (∀ d ∈ B3wit1.getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 (B3wit1.getD t []) ∧
    (readV (B3wit1.getD t []) (initV 1)).map acoef = B3tup1.getD t [] := by
  sorry

/-- From an automaton certificate to the response set of a column. -/
theorem resp_of_cert (c' : Fin 2) (A B : List (List St3)) (tA tB : List (List ℕ)) (out : List ℕ)
    (tup : List (List (ZMod 3))) (N M T : ℕ) (hN : A.length = N) (hM : B.length = M) (hM0 : 0 < M)
    (hinit : B.getD 0 [] = initV c')
    (hA : ∀ s : Fin N, ∀ r : Fin 3, (tA.getD s []).getD r 0 < N ∧
      stepV r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepV 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepV r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) [])
    (hread : ∀ s : Fin N, out.getD s 0 < T ∧ (A.getD s []).map acoef = tup.getD (out.getD s 0) [])
    (l : ℕ) (hl : 1 ≤ l) : ∃ t < T, vals (initV c') l = tup.getD t [] := by
  sorry

/-- **`prop:automaton` for `thm:B3`** (`j = 6`): for every carry length `l ≥ 1` and source coordinate
`c'`, the column of responses `(D_i(l)[c][c'])_{i<6, c<2}` is one of the `B3ntup c'` listed tuples. -/
theorem B3_resp (c' : Fin 2) (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < B3ntup c', ∀ i < 6, ∀ c : Fin 2, lawD B3g B3z B3G i l c c' = B3tupv c' t i c := by
  sorry

/-- **`prop:automaton` for `thm:B3`, exactness**: every listed tuple occurs for some `l ≥ 1`. -/
theorem B3_resp_occurs (c' : Fin 2) (t : ℕ) (ht : t < B3ntup c') :
    ∃ l, 1 ≤ l ∧ ∀ i < 6, ∀ c : Fin 2, lawD B3g B3z B3G i l c c' = B3tupv c' t i c := by
  sorry

theorem b3_distinct0 : ∀ t t' : Fin 24, t ≠ t' →
    ∃ i : Fin 6, ∃ c : Fin 2, B3tupv 0 t i c ≠ B3tupv 0 t' i c := by
  sorry

theorem b3_distinct1 : ∀ t t' : Fin 36, t ≠ t' →
    ∃ i : Fin 6, ∃ c : Fin 2, B3tupv 1 t i c ≠ B3tupv 1 t' i c := by
  sorry

/-- **`prop:automaton` for `thm:B3`, the count** (`j = 6`): the columns of responses over all carry
lengths `l ≥ 1` form a set of exactly `24` (`c' = 0`) resp. `36` (`c' = 1`) elements. -/
theorem B3_resp_card (c' : Fin 2) :
    Set.ncard {D : Fin 6 → Fin 2 → ZMod 3 |
      ∃ l, 1 ≤ l ∧ ∀ i : Fin 6, ∀ c : Fin 2, D i c = lawD B3g B3z B3G i l c c'} = B3ntup c' := by
  sorry

/-- **`thm:B3`, the certificate minimum** (`lem:cert`, `q = 3`, `j = 6`; computer-assisted in the
paper): for every step `e ∈ {-1,0,1}² ∖ {0}` and all carry lengths `l_c ≥ 1`,
`∑_c (3^6 f_6(e_c, σ_c))² ≥ 37865`, and `37865 = 91² + 172²` is attained at the antidiagonal step
`e = (1, -1)` with carry lengths `l = (1, 9)`. -/
theorem B3_cert_min :
    (∀ (e : Fin 2 → ℤ) (l : Fin 2 → ℕ), (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
      (∀ c, 1 ≤ l c) →
        37865 ≤ ∑ c, gapNum (zcode 3) 6 (e c) (certSigmaP (lawD B3g B3z B3G) 6 e l c) ^ 2) ∧
    ∑ c, gapNum (zcode 3) 6 (![1, -1] c) (certSigmaP (lawD B3g B3z B3G) 6 ![1, -1] ![1, 9] c) ^ 2 =
      37865 := by
  sorry

/-- **`thm:B3`, level `K = 1`**: `c(P_2) ≥ √37865/729` (every pair of the nine points has a coordinate
with toroidal gap `≥ 99/729`, so `c(P_2) ≥ 297/729 = 0.407`). -/
theorem B3_sep_one : SepAtLevel 3 2 1 (seqPoint (zcode 3) B3gen) (Real.sqrt 37865 / 729) := by
  sorry

/-- **`thm:B3`** (separation): `c(P_{2K}) ≥ √37865/729 = 0.266926…` for every `K ≥ 1`. -/
theorem B3_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 3 2 K (seqPoint (zcode 3) B3gen) (Real.sqrt 37865 / 729) := by
  sorry

/-- **`thm:B3`** (all `N`): `δ(P_{[N]}) ≥ 0.0889 · N^{-1/2}` for every `N ≥ 2`. -/
theorem B3_allN : SepAllN 2 (seqPoint (zcode 3) B3gen) (889 / 10000) := by
  sorry

/-- **`thm:B3`** (mesh ratio): `h(P_{[N]}) ≤ 16 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem B3_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 3) B3gen)) ≤
      16 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 3) B3gen))) := by
  sorry

/-- **`cor:allprimes`**: for every prime `p` there is an explicit scramble of the Faure sequence in
base `p` with algebraic multipliers in closed form that is a `(0,2)`-sequence with
`c(P_{2K}) ≥ 0.3678` (`p = 2`, `thm:B2`), `≥ 0.2669` (`p = 3`, `thm:B3`) and `≥ (p-3)/(2p)`
(`p ≥ 5`, both brick walls `W^±`, `thm:WF`) for every `K ≥ 1`. -/
theorem allprimes :
    (IsSeq0 (zcode 2) B2gen ∧
      ∀ K, 1 ≤ K → SepAtLevel 2 2 K (seqPoint (zcode 2) B2gen) (3678 / 10000)) ∧
    (IsSeq0 (zcode 3) B3gen ∧
      ∀ K, 1 ≤ K → SepAtLevel 3 2 K (seqPoint (zcode 3) B3gen) (2669 / 10000)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ a : ZMod p, (a = 1 ∨ a = -1) →
      IsSeq0 (zcode p) (WFgen p a) ∧
        ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p))) := by
  sorry

/-- **`cor:allprimes`** (quasi-uniform form): for every prime `p` there is an explicit `(0,2)`-sequence
in base `p` (`thm:B2`, `thm:B3`, `thm:WF`) with `c(P_{2K}) ≥ LB > 0` for all `K ≥ 1`,
`δ(P_{[N]}) ≥ b N^{-1/2}` for all `N ≥ 2`, and a bounded mesh ratio `h ≤ κ δ` along all `N`. -/
theorem allprimes_qu (p : ℕ) [hp : Fact p.Prime] :
    ∃ (C : Gen 2 (ZMod p)) (LB b κ : ℝ), 0 < LB ∧ 0 < b ∧ IsSeq0 (zcode p) C ∧
      (∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) C) LB) ∧
      SepAllN 2 (seqPoint (zcode p) C) b ∧
      ∀ N, 2 ≤ N → Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
        κ * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  sorry

end GeoSeq
