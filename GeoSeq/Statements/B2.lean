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
# Statements: base two (`thm:B2`, `eq:B2G`, `lem:octave`), GeoSeq stages S0, S1, S5

The sequence over `𝔽_2` with `y_{0,n} = [x^n](1+x)(1+u)V(u)` and `y_{1,n} = [x^n](u/x)V(1+u)`,
`u = ∑_k x^{2^k}` (`B2gen`). All statements PROVED: `B2_net` (`t = 0`, stage S1,
`GeoSeq/FrameNets.lean`); stage S5 (`GeoSeq/B2Law.lean`, `GeoSeq/B2Cert.lean`): `B2_root`
(`u² + u = x`), `B2_frame_inv` (`eq:B2G`), `B2_law` (`prop:law` for `B2gen`), `B2_ghat` (the
coefficient formulas of `Ĝ`), `B2_octave`, `B2_octave_count` (`lem:octave`), `B2_cert_min` (the
certificate minimum `2269618` at `j = 12`, attained), `B2_sep_one` (`K = 1`), `B2_sep`
(`c(P_{2K}) ≥ √2269618/4096` for every `K ≥ 1`), `B2_allN` (`δ(P_{[N]}) ≥ 0.1839 N^{-1/2}`),
`B2_mesh` (`h/δ ≤ 7.7` along all `N`). The claim that every prefix `P_m` is `κ_m`-separated
(`κ_m = ⌈m/2⌉ + 3`) is not stated.
-/

namespace GeoSeq

open Finset PowerSeries

/-- **`thm:B2`** (`t = 0`): the base-2 sequence is a `(0,2)`-sequence. -/
theorem B2_net : IsSeq0 (zcode 2) B2gen := by
  sorry

/-- **`thm:B2`**: the lacunary series `u = ∑_k x^{2^k}` satisfies `u² + u = x` over `𝔽_2`. -/
theorem B2_root : uB2 ^ 2 + uB2 = X := by
  sorry

/-- **`eq:B2G`**: `M G = 1` and `G M = 1` for the frame matrix `M = ((g_0, g_0 u), (g_1, g_1(1+u)))`
of `thm:B2` and `G = B2G`. -/
theorem B2_frame_inv : frameM B2g B2z * B2G = 1 ∧ B2G * frameM B2g B2z = 1 := by
  sorry

/-- **`thm:B2`, the law** (`prop:law`): at every level `K` and carry length `1 ≤ l ≤ K`, the carry
response `D_i(l)[c][c']` of the base-2 sequence is `lawD B2g B2z B2G i l c c'` (independent of `K`). -/
theorem B2_law (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin 2) :
    IsCarryEntry B2gen K i l c c' (lawD B2g B2z B2G i l c c') := by
  sorry

/-- **`lem:octave`, coefficient formulas** of `Ĝ = G/(1+x)` for `n ≥ 1`, read modulo `2`:
`[x^n] 1/(1+x²) = [n even]`, `[x^n] x/(1+x) = 1`, `[x^n](1+u)/(1+x) = ⌊log₂ n⌋`,
`[x^n] u/(x(1+x²)) = 1` for `n+1` odd and `⌊log₂(n+1)⌋` for `n+1` even. -/
theorem B2_ghat (n : ℕ) (hn : 1 ≤ n) :
    coeff n (B2G 0 0 * PowerSeries.mk 1) = (if n % 2 = 0 then 1 else 0) ∧
      coeff n (B2G 0 1 * PowerSeries.mk 1) = 1 ∧
      coeff n (B2G 1 1 * PowerSeries.mk 1) = ((Nat.log 2 n : ℕ) : ZMod 2) ∧
      coeff n (B2G 1 0 * PowerSeries.mk 1) =
        if (n + 1) % 2 = 1 then 1 else ((Nat.log 2 (n + 1) : ℕ) : ZMod 2) := by
  sorry

/-- **`lem:octave`**: for every carry length `l ≥ 1` there is `1 ≤ l' ≤ 63` with the same `12`-digit
responses: `D_i(l) = D_i(l')` for all `i < 12` (hence for every `j ≤ 12`). -/
theorem B2_octave (l : ℕ) (hl : 1 ≤ l) :
    ∃ l', 1 ≤ l' ∧ l' ≤ 63 ∧ ∀ i < 12, ∀ c c' : Fin 2,
      lawD B2g B2z B2G i l c c' = lawD B2g B2z B2G i l' c c' := by
  sorry

/-- **`lem:octave`, the count**: for `j = 12` the tuples `(D_i(l))_{i<12}`, `1 ≤ l ≤ 63` (hence, by
`B2_octave`, all `l ≥ 1`), take exactly `35` distinct values. -/
theorem B2_octave_count :
    ((Finset.Icc 1 63).image fun l => fun (i : Fin 12) (c c' : Fin 2) => lawD B2g B2z B2G i l c c').card
      = 35 := by
  sorry

/-- **`thm:B2`, the certificate minimum** (`lem:cert`, `q = 2`, `j = 12`; computer-assisted in the
paper): for every step `e ∈ {-1,0,1}² ∖ {0}` and all carry lengths `l_c ≥ 1`,
`∑_c (2^12 f_12(e_c, σ_c))² ≥ 2269618`, and the value `2269618 = 103² + 1503²` is attained at the
horizontal step `e = (1, 0)` with carry length `1`. -/
theorem B2_cert_min :
    (∀ (e : Fin 2 → ℤ) (l : Fin 2 → ℕ), (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
      (∀ c, 1 ≤ l c) →
        2269618 ≤ ∑ c, gapNum (zcode 2) 12 (e c) (certSigmaP (lawD B2g B2z B2G) 12 e l c) ^ 2) ∧
    ∑ c, gapNum (zcode 2) 12 (![1, 0] c) (certSigmaP (lawD B2g B2z B2G) 12 ![1, 0] ![1, 1] c) ^ 2 =
      2269618 := by
  sorry

/-- **`thm:B2`, level `K = 1`**: the four points of `P_2` have `c(P_2) ≥ √2269618/4096` (in fact every
pair has a coordinate with toroidal gap `≥ 79/256`, so `c(P_2) ≥ 158/256`). -/
theorem B2_sep_one : SepAtLevel 2 2 1 (seqPoint (zcode 2) B2gen) (Real.sqrt 2269618 / 4096) := by
  sorry

/-- **`thm:B2`** (separation): `c(P_{2K}) ≥ √2269618/4096 = 0.36780…` for every `K ≥ 1`. -/
theorem B2_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 2 2 K (seqPoint (zcode 2) B2gen) (Real.sqrt 2269618 / 4096) := by
  sorry

/-- **`thm:B2`** (all `N`): `δ(P_{[N]}) ≥ 0.1839 · N^{-1/2}` for every `N ≥ 2`. -/
theorem B2_allN : SepAllN 2 (seqPoint (zcode 2) B2gen) (1839 / 10000) := by
  sorry

/-- **`thm:B2`** (mesh ratio): `h(P_{[N]}) ≤ 7.7 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal; `15.4` in the convention `h/(δ/2)` of [DGS2]). -/
theorem B2_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 2) B2gen)) ≤
      (77 / 10) * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 2) B2gen))) := by
  sorry

end GeoSeq
