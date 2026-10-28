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
public import GeoSeq.S3Defs
public import GeoSeq.S3Data

@[expose] public section

/-!
# Statements: the Artin–Schreier frame `H = 𝔽_3` in dimension three (`thm:S3`, `lem:frames`(a) for `H = 𝔽_3`), GeoSeq stage S8

All PROVED (`GeoSeq/S3Auto.lean`, `S3Law.lean`, `S3Gap.lean`, `S3Check.lean`, `S3Cert*.lean`; generated verbatim
from the proof files' signatures).
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`lem:frames`(a) for `H = 𝔽_3`** (`S3_frames` with `IsP3` unfolded): `U = -∑_{k≥0} x^{3^k}` satisfies
`U³ - U = x`, `U(0) = 0`, the Mahler equation `U(x) = U(x³) - x`, and `[x^n] U = -1` exactly at the powers
of `3` (`0` otherwise). -/
theorem S3_frames_char : U3 ^ 3 - U3 = X ∧ constantCoeff U3 = 0 ∧ U3 = expand 3 three_ne_zero U3 - X ∧
    (∀ k, coeff (3 ^ k) U3 = -1) ∧ ∀ n, (¬ ∃ k, 3 ^ k = n) → coeff n U3 = 0 := by
  sorry

/-- **The Cartier step** (`prop:automaton`, proof, Artin–Schreier case): for `r < 3`, coefficient
`3n + r` of a state is coefficient `n` of `stepS r` of it. -/
theorem cartier_stepS (S : StS) (n r : ℕ) (hr : r < 3) :
    coeff (3 * n + r + 8) (esemS S) = coeff (n + 8) (esemS (stepS r S)) := by
  sorry

/-- **Closure ⟹ reachability** (states after a nonzero digit, `thm:S3`). -/
theorem reach_AS (A : List (List StS)) (tbl : List (List ℕ)) (N : ℕ)
    (h : ∀ s : Fin N, ∀ r : Fin 3, (tbl.getD s []).getD r 0 < N ∧
      stepVS r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ valsS (A.getD s []) n = valsS (A.getD s' []) 0 := by
  sorry

/-- **Closure ⟹ reachability** (states before the first nonzero digit, `thm:S3`). -/
theorem reach_BS (A B : List (List StS)) (tA tB : List (List ℕ)) (N M : ℕ)
    (hA : ∀ s : Fin N, ∀ r : Fin 3, (tA.getD s []).getD r 0 < N ∧
      stepVS r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepVS 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepVS r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ valsS (B.getD s []) n = valsS (A.getD s' []) 0 := by
  sorry

/-- `enc(σ ⊕ τ) = add3W (enc σ) (enc τ)` over `𝔽_3`. -/
theorem encVec_add3 {j : ℕ} (σ τ : Fin j → ZMod 3) :
    encVec (zcode 3) (σ + τ) = add3W j (encVec (zcode 3) σ) (encVec (zcode 3) τ) := by
  sorry

/-- `enc(-σ) = enc(2σ) = neg3W (enc σ)` over `𝔽_3`. -/
theorem encVec_two3 {j : ℕ} (σ : Fin j → ZMod 3) :
    encVec (zcode 3) (fun i => 2 * σ i) = neg3W j (encVec (zcode 3) σ) := by
  sorry

/-- The leading `n` digits of a digitwise sum are the digitwise sum of the leading digits. -/
theorem add3W_div (n k a b : ℕ) : add3W (n + k) a b / 3 ^ k = add3W n (a / 3 ^ k) (b / 3 ^ k) := by
  sorry

/-- **`thm:S3`**: `M G = 1` for the frame matrix `M[c][b] = g (c + U)^b` and `G = S3G`. -/
theorem S3_frame_inv : frameM (fun _ => S3g) S3z * S3G = 1 := by
  sorry

/-- **`thm:S3`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the sequence is `lawD (fun _ => g) z G i l c c'` (independent of `K`). -/
theorem S3_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 3) :
    IsCarryEntry S3gen K i l c c' (lawD (fun _ => S3g) S3z S3G i l c c') := by
  sorry

/-- **`thm:S3`** (`t = 0`): the sequence is a `(0,3)`-sequence in base `3`. -/
theorem S3_net : IsSeq0 (zcode 3) S3gen := by
  sorry

/-- **`thm:S3`**: the sequence is a scramble `(L_0 P_0, L_1 P_1, L_2 P_2)` of the Faure sequence in
base `3` (`C_c = L_c P_c`, places `0, 1, 2`, `L_c[n][i] = [x^n] g U^i`). -/
theorem S3_faure : S3gen = scrGen (fun c : Fin 3 => ((c : ℕ) : ZMod 3)) (ssScr (fun _ => S3g) S3z) := by
  sorry

/-- **`thm:S3`, the frame matrix in closed form**: `(1 - x) M[c][b] = P_0 + P_1 U + P_2 U²` with the
numerators `S3Mn c b`. -/
theorem S3_M (c b : Fin 3) : (1 - X) * frameM (fun _ => S3g) S3z c b = tsemS (S3Mn c b) := by
  sorry

/-- **`thm:S3`, `Ĝ` in closed form**: `x Q_p Ĝ[b][c'] = P_0 + P_1 U + P_2 U²` with the numerators
`S3An b c'`. -/
theorem S3_ghat (b c' : Fin 3) :
    X * lps QpS * (S3G b c' * PowerSeries.mk 1) = tsemS (S3An b c') := by
  sorry

/-- **The initial states** (`prop:automaton`, proof): `esemS (initSS i c c') = x^{8-i} F_i[c][c']`. -/
theorem esemS_init (i : ℕ) (hi : i < 8) (c c' : Fin 3) :
    esemS (initSS i c c') = X ^ (8 - i) * S3F i c c' := by
  sorry

/-- **The initial states read the responses**: coefficient `l` of the initial state of entry
`(c, c')`, depth `i < 8`, is the carry response `D_i(l)[c][c']` of `prop:law`. -/
theorem S3_init (i : ℕ) (hi : i < 8) (c c' : Fin 3) (l : ℕ) :
    coeff (l + 8) (esemS (initSS i c c')) = lawD (fun _ => S3g) S3z S3G i l c c' := by
  sorry

/-- **`prop:automaton` for `thm:S3`** (`j = 8`): for every carry length `l ≥ 1` and source coordinate
`c'`, the column `(D_i(l)[c][c'])_{i<8, c<3}` is one of the `85` listed columns of source `c'`. -/
theorem S3_resp (c' : Fin 3) (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < 85, ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => S3g) S3z S3G i l c c' = S3tupv c' t (3 * i + c) := by
  sorry

/-- **`prop:automaton` for `thm:S3`, exactness**: every listed column occurs for some `l ≥ 1`. -/
theorem S3_resp_occurs (c' : Fin 3) (t : ℕ) (ht : t < 85) :
    ∃ l, 1 ≤ l ∧ ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => S3g) S3z S3G i l c c' = S3tupv c' t (3 * i + c) := by
  sorry

/-- **`prop:automaton` for `thm:S3`, the count** (`j = 8`): for every source coordinate `c'`, the columns
over all carry lengths `l ≥ 1` form a set of exactly `85` elements. -/
theorem S3_resp_card (c' : Fin 3) :
    Set.ncard {D : Fin 8 → Fin 3 → ZMod 3 |
      ∃ l, 1 ≤ l ∧ ∀ i : Fin 8, ∀ c : Fin 3, D i c = lawD (fun _ => S3g) S3z S3G i l c c'} = 85 := by
  sorry

theorem s3_check (f0 f1 f2 : ℕ) (h0 : f0 < 3) (h1 : f1 < 3) (h2 : f2 < 3) (hne : f0 ≠ 0 ∨ f1 ≠ 0 ∨ f2 ≠ 0) :
    (f0 ≠ 0 → f1 ≠ 0 → f2 ≠ 0 → s3full f0 f1 f2 = true) ∧
    (f0 = 0 ∨ f1 = 0 ∨ f2 = 0 → s3part f0 f1 f2 = true) := by
  sorry

/-- The lower-bound half of the certificate of `thm:S3`: for every step and all carry lengths
`l_c ≥ 1`, `∑_c (3^8 f_8(e_c, σ_c))² ≥ 134917`. -/
theorem S3_cert_lb (e : Fin 3 → ℤ) (l : Fin 3 → ℕ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    134917 ≤ ∑ c, gapNum (zcode 3) 8 (e c) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l c) ^ 2 := by
  sorry

/-- **`thm:S3`, level `K = 1`**: `c(P_3) ≥ √134917/6561` (every pair of the `27` points has a coordinate
with toroidal gap `≥ 41/729`, so `c(P_3) ≥ 123/729 = 0.168`). -/
theorem S3_sep_one : SepAtLevel 3 3 1 (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561) := by
  sorry

/-- **`thm:S3`** (separation): `c(P_{3K}) ≥ √134917/3^8 = 0.0559839…` for every `K ≥ 1`. -/
theorem S3_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 3 3 K (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561) := by
  sorry

/-- **`thm:S3`** (all `N`): `δ(P_{[N]}) ≥ 0.0186 · N^{-1/3}` for every `N ≥ 2`. -/
theorem S3_allN : SepAllN 3 (seqPoint (zcode 3) S3gen) (186 / 10000) := by
  sorry

/-- **`thm:S3`** (mesh ratio): `h(P_{[N]}) ≤ 93 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem S3_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 3) S3gen)) ≤
      93 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 3) S3gen))) := by
  sorry

end GeoSeq
