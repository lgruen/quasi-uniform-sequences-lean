/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs
public import GeoSeq.F4
public import GeoSeq.K4Defs
public import GeoSeq.S4Defs
public import GeoSeq.S4SymDefs
public import GeoSeq.S4Data

@[expose] public section

/-!
# Statements: the Artin–Schreier frame `H = 𝔽_4` in dimension four (`thm:S4`, `lem:frames`(a) for `H = 𝔽_4`), GeoSeq stage S8

All PROVED (`GeoSeq/S4Auto.lean`, `S4Law.lean`, `S4AutoA–D.lean`, `S4Check.lean`, `S4Cert.lean`; generated
verbatim from the proof files' signatures).
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`lem:frames`(a) for `H = 𝔽_4`** (`S4_frames` with `IsP4` unfolded): `U = ∑_{k≥0} x^{4^k}` satisfies
`U⁴ + U = x`, `U(0) = 0`, the Mahler equation `U(x) = U(x⁴) + x`, and `[x^n] U = 1` exactly at the powers
of `4` (`0` otherwise). -/
theorem S4_frames_char : U4 ^ 4 + U4 = X ∧ constantCoeff U4 = 0 ∧ U4 = expand 4 four_ne_zero U4 + X ∧
    (∀ k, coeff (4 ^ k) U4 = 1) ∧ ∀ n, (¬ ∃ k, 4 ^ k = n) → coeff n U4 = 0 := by
  sorry

/-- **The Cartier step** (`prop:automaton`, proof, Artin–Schreier case over `𝔽_4`): for `r < 4`,
coefficient `4n + r` of a state is coefficient `n` of `stepU r` of it. -/
theorem cartier_stepU (S : StU) (n r : ℕ) (hr : r < 4) :
    coeff (4 * n + r + 5) (esemU S) = coeff (n + 5) (esemU (stepU r S)) := by
  sorry

/-- **Closure ⟹ reachability** (states after a nonzero digit, `thm:S4`). -/
theorem reach_AU (A : List (List StU)) (tbl : List (List ℕ)) (N : ℕ)
    (h : ∀ s : Fin N, ∀ r : Fin 4, (tbl.getD s []).getD r 0 < N ∧
      stepVU r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ valsU (A.getD s []) n = valsU (A.getD s' []) 0 := by
  sorry

/-- **Closure ⟹ reachability** (states before the first nonzero digit, `thm:S4`). -/
theorem reach_BU (A B : List (List StU)) (tA tB : List (List ℕ)) (N M : ℕ)
    (hA : ∀ s : Fin N, ∀ r : Fin 4, (tA.getD s []).getD r 0 < N ∧
      stepVU r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepVU 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 4, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepVU r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ valsU (B.getD s []) n = valsU (A.getD s' []) 0 := by
  sorry

/-- **Conjugation invariance of the law** (any frame): if permuting the rows of the frame matrix by `σ`
is right multiplication by a constant matrix `P`, permuting the columns of `G` by `σ` is left
multiplication by `P`, and `P² = I`, then `D_i(l)[σc][σc'] = D_i(l)[c][c']`. -/
theorem lawD_conj {s : ℕ} {R : Type*} [CommRing R] (g zθ : Fin s → PowerSeries R)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (σ : Fin s → Fin s) (P : Fin s → Fin s → R)
    (hM : ∀ c b, frameM g zθ (σ c) b = ∑ b', C (P b' b) * frameM g zθ c b')
    (hG : ∀ b c', G b (σ c') = ∑ b'', C (P b b'') * G b'' c')
    (hP : ∀ b' b'', ∑ b, P b' b * P b b'' = if b' = b'' then 1 else 0)
    (hσ : ∀ c c', σ c = σ c' ↔ c = c') (i l : ℕ) (c c' : Fin s) :
    lawD g zθ G i l (σ c) (σ c') = lawD g zθ G i l c c' := by
  sorry

/-- **`thm:S4`**: `M G = 1` for the frame matrix `M[c][b] = g (a_c + U)^b` and `G = S4G`. -/
theorem S4_frame_inv : frameM (fun _ => S4g) S4z * S4G = 1 := by
  sorry

/-- **`thm:S4`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the sequence is `lawD (fun _ => g) z G i l c c'` (independent of `K`). -/
theorem S4_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 4) :
    IsCarryEntry S4gen K i l c c' (lawD (fun _ => S4g) S4z S4G i l c c') := by
  sorry

/-- **`thm:S4`** (`t = 0`): the sequence is a `(0,4)`-sequence in base `4`. -/
theorem S4_net : IsSeq0 f4code S4gen := by
  sorry

/-- **`thm:S4`, the frame matrix in closed form**: `M[c][b] = ∑_k P_k U^k` with the numerators
`S4Mn c b`. -/
theorem S4_M (c b : Fin 4) : frameM (fun _ => S4g) S4z c b = tsemU (S4Mn c b) := by
  sorry

/-- **`thm:S4`, `Ĝ` in closed form**: `Q_p Ĝ[b][c'] = ∑_k P_k U^k` with the numerators `S4An b c'`. -/
theorem S4_ghat (b c' : Fin 4) :
    lps QpU * (S4G b c' * PowerSeries.mk 1) = tsemU (S4An b c') := by
  sorry

/-- **`thm:S4`, translation symmetry**: `D_i(l)[c][c'] = D_i(l)[c ⊕ c'][0]` (the member is symmetric under
the translations `z ↦ z + h`, `h ∈ 𝔽_4`; `⊕` = XOR of the codes). -/
theorem S4_rot (i l : ℕ) (c c' : Fin 4) :
    lawD (fun _ => S4g) S4z S4G i l c c' = lawD (fun _ => S4g) S4z S4G i l (fxor c c') 0 := by
  sorry

/-- **The initial states** (`prop:automaton`, proof): `esemU (initSU i c c' sh) = x^{5-i+sh} F_i[c][c']`. -/
theorem esemU_init (i : ℕ) (hi : i < 5) (c c' : Fin 4) (sh : ℕ) :
    esemU (initSU i c c' sh) = X ^ (5 - i + sh) * S4F i c c' := by
  sorry

/-- Coefficient `l` of `initSU i c c' 0` is `D_i(l)[c][c']`. -/
theorem S4_init (i : ℕ) (hi : i < 5) (c c' : Fin 4) (l : ℕ) :
    coeff (l + 5) (esemU (initSU i c c' 0)) = lawD (fun _ => S4g) S4z S4G i l c c' := by
  sorry

/-- Coefficient `l ≥ 1` of `initSU i c c' 1` is `D_i(l-1)[c][c']`. -/
theorem S4_init1 (i : ℕ) (hi : i < 5) (c c' : Fin 4) (l : ℕ) (hl : 1 ≤ l) :
    coeff (l + 5) (esemU (initSU i c c' 1)) = lawD (fun _ => S4g) S4z S4G i (l - 1) c c' := by
  sorry

theorem s4_closeA : ∀ s : Fin 170, ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by
  sorry

theorem s4_read : ∀ s : Fin 170, S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by
  sorry

theorem s4_wit : ∀ t : Fin 80, (∀ d ∈ S4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (S4wit.getD t []) ∧ (readVU (S4wit.getD t []) (initVU 0)).map acoefU = (S4tup.getD t []).map n2f := by
  sorry

theorem s4_distinct : ∀ t : Fin 80, ∀ t' : Fin 80, t ≠ t' → ∃ k : Fin 40, S4tupv t k ≠ S4tupv t' k := by
  sorry

/-- **`prop:automaton` for `thm:S4`** (`j = 5`, source `0`): for every carry length `l ≥ 1` the pair
column `(D_i(l)[c][0], D_i(l-1)[c][0])_{i<5, c<4}` is one of the `80` listed tuples. -/
theorem S4_resp (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < 80, ∀ i < 5, ∀ c : Fin 4, lawD (fun _ => S4g) S4z S4G i l c 0 = S4tupv t (4 * i + c) ∧
      S4Dr i (l - 1) c 0 = S4tupv t (20 + 4 * i + c) := by
  sorry

/-- **`prop:automaton` for `thm:S4`, exactness**: every listed pair column occurs for some `l ≥ 1`. -/
theorem S4_resp_occurs (t : ℕ) (ht : t < 80) :
    ∃ l, 1 ≤ l ∧ ∀ i < 5, ∀ c : Fin 4, lawD (fun _ => S4g) S4z S4G i l c 0 = S4tupv t (4 * i + c) ∧
      S4Dr i (l - 1) c 0 = S4tupv t (20 + 4 * i + c) := by
  sorry

/-- **`prop:automaton` for `thm:S4`, the count** (`j = 5`): the pair columns
`(D_i(l)[c][0], D_i(l-1)[c][0])_{i<5, c<4}` over all `l ≥ 1` form a set of exactly `80` elements. -/
theorem S4_resp_card :
    Set.ncard {D : Fin 5 → Fin 4 → F4 × F4 | ∃ l, 1 ≤ l ∧ ∀ i : Fin 5, ∀ c : Fin 4,
      D i c = (lawD (fun _ => S4g) S4z S4G i l c 0, S4Dr i (l - 1) c 0)} = 80 := by
  sorry

/-- **The change columns of `thm:S4`** (`eq:carrychange`, `Δ(ȳ) = ω²`, `Δ(y) ∈ {1, ω²}`): for every carry
length `l ≥ 1` and stop digit `y`, the change of the geometric digit `K + i` of coordinate `c` caused by a
step of coordinate `c'` is entry `(i, c ⊕ c')` of one of the listed change columns of source `0`. -/
theorem S4_change (l : ℕ) (hl : 1 ≤ l) (y : F4) : ∃ t < 80, ∃ ty < 2, ∀ i < 5, ∀ c c' : Fin 4,
    carryChange f4code S4Dr i l y c c' = chgU t ty i (fxor c c') := by
  sorry

theorem s4_full : s4full = true := by
  sorry

/-- The lower-bound half of the certificate of `thm:S4`: for every step, all carry lengths `l_c ≥ 1` and
all stop digits `y`, `∑_c (4^5 f_5(e_c, σ_c))² ≥ 952`. -/
theorem S4_cert_lb (e : Fin 4 → ℤ) (l : Fin 4 → ℕ) (y : Fin 4 → F4)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    952 ≤ ∑ c, gapNum f4code 5 (e c) (certSigma f4code S4Dr 5 e l y c) ^ 2 := by
  sorry

/-- **`thm:S4`** (separation): `c(P_{4K}) ≥ √952/4^5 = 0.0301313…` for every `K ≥ 1`. -/
theorem S4_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 4 4 K (seqPoint f4code S4gen) (Real.sqrt 952 / 1024) := by
  sorry

/-- **`thm:S4`** (all `N`): `δ(P_{[N]}) ≥ 0.0075 · N^{-1/4}` for every `N ≥ 2`. -/
theorem S4_allN : SepAllN 4 (seqPoint f4code S4gen) (75 / 10000) := by
  sorry

/-- **`thm:S4`** (mesh ratio): `h(P_{[N]}) ≤ 266 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem S4_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint f4code S4gen)) ≤
      266 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint f4code S4gen))) := by
  sorry

end GeoSeq
