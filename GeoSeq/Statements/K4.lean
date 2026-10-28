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
public import GeoSeq.K4Data

@[expose] public section

/-!
# Statements: the Kummer frame over `𝔽_4` (`thm:K4`, `lem:frames`(b) for `q = 4`, `prop:automaton` for `thm:K4`), GeoSeq stage S8

All PROVED (`GeoSeq/K4Auto.lean`, `K4Law.lean`, `K4Gap.lean`, `K4Cert.lean`; generated verbatim from the proof
files' signatures).
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`lem:frames`(b) for `q = 4`**: `τ` (with `τ^{-1} = T4 = ∏_{i≥0}(1 + x^{4^i})`) satisfies
`τ³ = 1 + x`, `τ(0) = 1`; `T4` satisfies the Mahler equation `T4(x) = (1 + x) T4(x⁴)`, and
`[x^n] T4 = 1` exactly when every base-4 digit of `n` is `0` or `1` (`0` otherwise). -/
theorem K4_frames : tau4 * T4 = 1 ∧ tau4 ^ 3 = 1 + X ∧ constantCoeff tau4 = 1 ∧
    T4 = (1 + X) * expand 4 four_ne_zero T4 ∧
    ∀ n, coeff n T4 = if ∀ d ∈ Nat.digits 4 n, d ≤ 1 then 1 else 0 := by
  sorry

/-- **The Cartier step** (`prop:automaton`, proof, `q = 4`): for `r < 4`, coefficient `4n + r` of a
state is coefficient `n` of `stepP4 r` of it. -/
theorem cartier_step4 (S : St4) (n r : ℕ) (hr : r < 4) :
    coeff (4 * n + r + 8) (esem4 S) = coeff (n + 8) (esem4 (stepP4 r S)) := by
  sorry

/-- **Closure ⟹ reachability** (states after a nonzero digit, `q = 4`). -/
theorem reach_A4 (A : List (List St4)) (tbl : List (List ℕ)) (N : ℕ) (hN : A.length = N)
    (h : ∀ s : Fin N, ∀ r : Fin 4, (tbl.getD s []).getD r 0 < N ∧
      stepV4 r (A.getD s []) = A.getD ((tbl.getD s []).getD r 0) []) :
    ∀ n s, s < N → ∃ s', s' < N ∧ vals4 (A.getD s []) n = vals4 (A.getD s' []) 0 := by
  sorry

/-- **Closure ⟹ reachability** (states before the first nonzero digit, `q = 4`). -/
theorem reach_B4 (A B : List (List St4)) (tA tB : List (List ℕ)) (N M : ℕ) (hN : A.length = N)
    (hM : B.length = M)
    (hA : ∀ s : Fin N, ∀ r : Fin 4, (tA.getD s []).getD r 0 < N ∧
      stepV4 r (A.getD s []) = A.getD ((tA.getD s []).getD r 0) [])
    (hB : ∀ s : Fin M, ((tB.getD s []).getD 0 0 < M ∧
      stepV4 0 (B.getD s []) = B.getD ((tB.getD s []).getD 0 0) []) ∧
      ∀ r : Fin 4, r ≠ 0 → (tB.getD s []).getD r 0 < N ∧
        stepV4 r (B.getD s []) = A.getD ((tB.getD s []).getD r 0) []) :
    ∀ n s, 1 ≤ n → s < M → ∃ s', s' < N ∧ vals4 (B.getD s []) n = vals4 (A.getD s' []) 0 := by
  sorry

/-- `enc(a ⊕ b) = enc(a) XOR enc(b)` for digit vectors over `𝔽_4`. -/
theorem encVec_xor4 {j : ℕ} (a b : Fin j → F4) :
    encVec f4code (a + b) = encVec f4code a ^^^ encVec f4code b := by
  sorry

/-- `4^j f_j(±1, σ) ≥ 4^j − 1 − enc σ` over `𝔽_4`. -/
theorem gapNum4_pm (j : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) (σ : Fin j → F4) :
    4 ^ j - encVec f4code σ - 1 ≤ gapNum f4code j e σ := by
  sorry

/-- `4^j f_j(0, σ) ≥ topW j (enc σ) − 1` over `𝔽_4`. -/
theorem gapNum4_zero (j : ℕ) (σ : Fin j → F4) :
    topW j (encVec f4code σ) - 1 ≤ gapNum f4code j 0 σ := by
  sorry

/-- **`thm:K4`**: `M G = 1` for the frame matrix `M[c][b] = g (ω^c τ)^b` and `G = K4G`. -/
theorem K4_frame_inv : frameM (fun _ => K4g) K4z * K4G = 1 := by
  sorry

/-- **`thm:K4`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the sequence is `lawD (fun _ => g) z G i l c c'` (independent of `K`). -/
theorem K4_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 3) :
    IsCarryEntry K4gen K i l c c' (lawD (fun _ => K4g) K4z K4G i l c c') := by
  sorry

/-- **`thm:K4`** (`t = 0`): the sequence is a `(0,3)`-sequence in base `4`. -/
theorem K4_net : IsSeq0 f4code K4gen := by
  sorry

/-- **`thm:K4`, rotation symmetry**: `D_i(l)[c][c'] = D_i(l)[c - c'][0]`. -/
theorem K4_rot (i l : ℕ) (c c' : Fin 3) :
    lawD (fun _ => K4g) K4z K4G i l c c' = lawD (fun _ => K4g) K4z K4G i l (c - c') 0 := by
  sorry

/-- **`thm:K4`, the frame matrix in closed form**: `x g τ^b = P_0 + P_1 τ^{-1} + P_2 τ^{-2}` with the
numerators `K4Mn b`. -/
theorem K4_M (b : Fin 3) : X * (K4g * tau4 ^ (b : ℕ)) = tsem4 (K4Mn b) := by
  sorry

/-- **`thm:K4`, `Ĝ` in closed form**: `x (1 + x²) Ĝ[b][0] = P_0 + P_1 τ^{-1} + P_2 τ^{-2}` with the
numerators `K4An b`. -/
theorem K4_ghat (b : Fin 3) :
    X * lps Qp4 * (K4G b 0 * PowerSeries.mk 1) = tsem4 (K4An b) := by
  sorry

/-- **The initial states** (`prop:automaton`, proof): `esem4 (initS4 i c sh) = x^{8-i+sh} F_i[c][0]`. -/
theorem esem4_init (i : ℕ) (hi : i < 8) (c : Fin 3) (sh : ℕ) :
    esem4 (initS4 i c sh) = X ^ (8 - i + sh) * K4F i c 0 := by
  sorry

/-- **The initial states read the responses**: coefficient `l` of `initS4 i c 0` is `D_i(l)[c][0]`. -/
theorem K4_init (i : ℕ) (hi : i < 8) (c : Fin 3) (l : ℕ) :
    coeff (l + 8) (esem4 (initS4 i c 0)) = lawD (fun _ => K4g) K4z K4G i l c 0 := by
  sorry

/-- Coefficient `l ≥ 1` of `initS4 i c 1` is `D_i(l-1)[c][0]`. -/
theorem K4_init1 (i : ℕ) (hi : i < 8) (c : Fin 3) (l : ℕ) (hl : 1 ≤ l) :
    coeff (l + 8) (esem4 (initS4 i c 1)) = lawD (fun _ => K4g) K4z K4G i (l - 1) c 0 := by
  sorry

theorem k4_init : K4Bv.getD 0 [] = initV4 := by
  sorry

theorem k4_closeA : ∀ s : Fin 51, ∀ r : Fin 4, (K4tA.getD s []).getD r 0 < 51 ∧
    stepV4 r (K4Av.getD s []) = K4Av.getD ((K4tA.getD s []).getD r 0) [] := by
  sorry

theorem k4_closeB : ∀ s : Fin 3, ((K4tB.getD s []).getD 0 0 < 3 ∧
    stepV4 0 (K4Bv.getD s []) = K4Bv.getD ((K4tB.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 4, r ≠ 0 → (K4tB.getD s []).getD r 0 < 51 ∧
      stepV4 r (K4Bv.getD s []) = K4Av.getD ((K4tB.getD s []).getD r 0) [] := by
  sorry

theorem k4_read : ∀ s : Fin 51, K4out.getD s 0 < 37 ∧
    (K4Av.getD s []).map acoef4 = (K4tup.getD (K4out.getD s 0) []).map n2f := by
  sorry

theorem k4_wit : ∀ t : Fin 37, (∀ d ∈ K4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (K4wit.getD t []) ∧
    (readV4 (K4wit.getD t []) initV4).map acoef4 = (K4tup.getD t []).map n2f := by
  sorry

/-- `D_i(0) = 0` from the formula: coefficient `0` of every initial state vanishes. -/
theorem k4_zero : ∀ i : Fin 8, ∀ c : Fin 3, acoef4 (initS4 i c 0) = 0 := by
  sorry

theorem k4_distinct : ∀ t t' : Fin 37, t ≠ t' → ∃ k : Fin 48, K4tupv t k ≠ K4tupv t' k := by
  sorry

/-- **`prop:automaton` for `thm:K4`** (`j = 8`, source `0`): for every carry length `l ≥ 1` the pair
column `(D_i(l)[c][0], D_i(l-1)[c][0])_{i<8, c<3}` is one of the `37` listed tuples. -/
theorem K4_resp (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < 37, ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => K4g) K4z K4G i l c 0 = K4tupv t (3 * i + c) ∧
      K4Dr i (l - 1) c 0 = K4tupv t (24 + 3 * i + c) := by
  sorry

/-- **`prop:automaton` for `thm:K4`, exactness**: every listed pair tuple occurs for some `l ≥ 1`. -/
theorem K4_resp_occurs (t : ℕ) (ht : t < 37) :
    ∃ l, 1 ≤ l ∧ ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => K4g) K4z K4G i l c 0 = K4tupv t (3 * i + c) ∧
      K4Dr i (l - 1) c 0 = K4tupv t (24 + 3 * i + c) := by
  sorry

/-- **`prop:automaton` for `thm:K4`, the count** (`j = 8`): the pair columns
`(D_i(l)[c][0], D_i(l-1)[c][0])_{i<8, c<3}` over all `l ≥ 1` form a set of exactly `37` elements. -/
theorem K4_resp_card :
    Set.ncard {D : Fin 8 → Fin 3 → F4 × F4 | ∃ l, 1 ≤ l ∧ ∀ i : Fin 8, ∀ c : Fin 3,
      D i c = (lawD (fun _ => K4g) K4z K4G i l c 0, K4Dr i (l - 1) c 0)} = 37 := by
  sorry

/-- **The change columns of `thm:K4`** (`eq:carrychange`, `Δ(ȳ) = ω²`, `Δ(y) ∈ {1, ω²}`): for every
carry length `l ≥ 1` and stop digit `y`, the change of the geometric digit `K + i` of coordinate `c`
caused by a step of coordinate `c'` is the entry `(i, c - c')` of one of the listed change columns
(`ω² D(l)` or `D(l) + ω D(l-1)` of a listed pair tuple, rotated). -/
theorem K4_change (l : ℕ) (hl : 1 ≤ l) (y : F4) : ∃ t < 37, ∃ ty < 2, ∀ i < 8, ∀ c c' : Fin 3,
    carryChange f4code K4Dr i l y c c' = chgF t ty i (c - c') := by
  sorry

/-- The words of the change columns (`K4Z`, one word per target offset). -/
theorem k4_chg : ∀ t : Fin 37, ∀ ty : Fin 2, ∀ c : Fin 3, (K4chg.getD t []).getD ty 0 < 67 ∧
    encVec f4code (fun i : Fin 8 => chgF t ty i c) = (K4Z.getD ((K4chg.getD t []).getD ty 0) []).getD c 0 := by
  sorry

/-- The certificate check for the moving sets with one or two coordinates. -/
theorem k4_check_part : ∀ m0 m1 m2 : Bool, (m0 && m1 && m2) = false → (m0 || m1 || m2) = true →
    k4chk m0 m1 m2 = true := by
  sorry

/-- The certificate check for the steps that move all three coordinates (`67³` choices). -/
theorem k4_check_full : k4chk true true true = true := by
  sorry

/-- The lower-bound half of `K4_cert_min`: for every step, all carry lengths `l_c ≥ 1` and all stop
digits `y`, `∑_c (4^8 f_8(e_c, σ_c))² ≥ 54774953`. -/
theorem K4_cert_lb (e : Fin 3 → ℤ) (l : Fin 3 → ℕ) (y : Fin 3 → F4)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    54774953 ≤ ∑ c, gapNum f4code 8 (e c) (certSigma f4code K4Dr 8 e l y c) ^ 2 := by
  sorry

/-- **`thm:K4`** (separation): `c(P_{3K}) ≥ √54774953/4^8 = 0.1129305…` for every `K ≥ 1`. -/
theorem K4_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 4 3 K (seqPoint f4code K4gen) (Real.sqrt 54774953 / 65536) := by
  sorry

/-- **`thm:K4`** (all `N`): `δ(P_{[N]}) ≥ 0.0282 · N^{-1/3}` for every `N ≥ 2`. -/
theorem K4_allN : SepAllN 3 (seqPoint f4code K4gen) (282 / 10000) := by
  sorry

/-- **`thm:K4`** (mesh ratio): `h(P_{[N]}) ≤ 61.4 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem K4_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint f4code K4gen)) ≤
      614 / 10 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint f4code K4gen))) := by
  sorry

end GeoSeq
