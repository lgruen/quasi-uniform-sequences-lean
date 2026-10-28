/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs

@[expose] public section

/-!
# Statements: stages V9-1, V9-2 (paper V4: `lem:resform`, `sec:residueseq`, `lem:prefix`)

The residue identity (`lem:resform` (a), (c)), residue sequences (`def:residue`, `lem:residue-t0`, `lem:residue-rel`), `thm:residue`, `cor:korobov`, `cor:residueQU` and the prefix lemma for level families (`lem:prefix`, `rem:prefixcases`).
PROVED (`GeoSeq/V9Res.lean`, `V9Seq.lean`, `V9Prefix.lean`, `V9Thm.lean`, `V9Kor.lean`, `V9QU.lean`); generated verbatim from the
proof files' signatures by `scripts/gen_v9_statements.py` (definitions in `GeoSeq/V9Defs.lean`). Paper: V4
(`paper/sections/04-law.tex`, `05-residue.tex`, `02-prelim.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV9.json`.
-/

namespace GeoSeq
open Finset Polynomial

section G0
variable {F : Type*} [Field F] {s : ℕ}

/-- **`lem:resform`(c)** (residue theorem on the projective line): for distinct places `a_c` and every
`F = V / ∏_c (z - a_c)^{k_c}`, `∑_c Res_{a_c}(F dz) = [z^{-1}] F`. -/
theorem res_thm (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (V : F[X]) :
    ∑ c, resAt a k V c = resInf a k V := by
  sorry

/-- `lem:resform`(c), first case: if `deg V < M = ∑_c k_c`, then `[z^{-1}] F = [z^{M-1}] V`. -/
theorem res_thm_of_deg (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (V : F[X])
    (hV : V.natDegree < ∑ c, k c) :
    ∑ c, resAt a k V c = V.coeff (∑ c, k c - 1) := by
  sorry

/-- `lem:resform`(c), "in particular": the residues add up to `0` when `deg V ≤ ∑_c k_c - 2`
(`F = O(z^{-2})` at `∞`). -/
theorem res_thm_zero (a : Fin s → F) (ha : Function.Injective a) (k : Fin s → ℕ) (V : F[X])
    (hV : V.natDegree + 2 ≤ ∑ c, k c) :
    ∑ c, resAt a k V c = 0 := by
  sorry

/-- A Taylor digit is a residue: `[(z - a)^k] V = Res_a(V (z - a)^{-k-1} dz)` (`sec:prelim`). -/
theorem locRes_one (a : F) (k : ℕ) (V : F[X]) : locRes a (k + 1) V 1 = (taylor a V).coeff k := by
  sorry

/-- The Taylor coefficients of the index polynomial are the unscrambled frame digits:
`[(z - a)^i] V = ∑_j P_a[i][j] V_j`. -/
theorem taylor_coeff_vecPoly (a : F) (f : ℕ → F) (m i : ℕ) :
    (taylor a (vecPoly f m)).coeff i = ∑ j ∈ range m, pas a i j * f j := by
  sorry

/-- **`lem:resform`(a)**: for every scramble `L` of the frame, digit `n` of coordinate `c` of the
point with index digits `f_0, …, f_{m-1}` is `∑_{k ≤ n} L_c[n][k] Res_{a_c}(V (z - a_c)^{-k-1} dz)`, the
residue of the index polynomial `V` against the polar differential
`η_{c,n} = ∑_{k ≤ n} L_c[n][k] (z - a_c)^{-k-1} dz` (residues are linear in the differential). -/
theorem scrGen_res (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : ℕ → F) (m : ℕ) (c : Fin s)
    (n : ℕ) :
    ∑ j ∈ range m, scrGen a L c n j * f j =
      ∑ k ∈ range (n + 1), L c n k * locRes (a c) (k + 1) (vecPoly f m) 1 := by
  sorry

/-- `P(a) = l_n`: the polar differential `P(z) (z - a)^{-n-1} dz` has exact pole order `n + 1` iff
`l_n ≠ 0` (for a scramble, `L_c[n][n] ≠ 0`). -/
theorem polarNum_eval (a : F) (l : ℕ → F) (n : ℕ) : (polarNum a l n).eval a = l n := by
  sorry

/-- **`lem:resform`(a)**, one residue: digit `n` of coordinate `c` is `Res_{a_c}(V η_{c,n})` with the polar
differential `η_{c,n} = P_{c,n}(z) (z - a_c)^{-n-1} dz`, `P_{c,n} = ∑_{k ≤ n} L_c[n][k] (z - a_c)^{n-k}`
(`polarNum`), of exact pole order `n + 1` iff `L_c[n][n] ≠ 0` (`polarNum_eval`). -/
theorem scrGen_res_polar (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : ℕ → F) (m : ℕ) (c : Fin s)
    (n : ℕ) :
    ∑ j ∈ range m, scrGen a L c n j * f j =
      locRes (a c) (n + 1) (vecPoly f m * polarNum (a c) (L c n) n) 1 := by
  sorry

end G0

section G1
variable {F : Type*} [Field F] {s : ℕ}

/-- **`def:residue`** (matrix form): `C_c[n][i] = v_c^{-1} θ^{n+1} [(z - a_c)^n] z^i / w_c(z)^{n+1}`, the
coefficient of `t^n` in `(a_c + t)^i · w_c(a_c + t)^{-(n+1)}`. -/
theorem resSeq_apply (a : Fin s → F) (θ : F) (v : Fin s → F) (c : Fin s) (n i : ℕ) :
    resSeq a θ v c n i = (v c)⁻¹ * θ ^ (n + 1) * PowerSeries.coeff n
      ((taylor (a c) (X ^ i) : PowerSeries F) *
        ((taylor (a c) (wCo a c) : PowerSeries F)⁻¹) ^ (n + 1)) := by
  sorry

/-- **`def:residue`** (residue reading): digit `n` of coordinate `c` of the point with index digits
`f_0, …, f_{m-1}` is `y_{c,n}(V) = v_c^{-1} Res_{a_c}(V (θ/w)^{n+1} dz)
= v_c^{-1} θ^{n+1} Res_{a_c}(V / ((z - a_c)^{n+1} w_c^{n+1}) dz)`. -/
theorem resSeq_digit (a : Fin s → F) (θ : F) (v : Fin s → F) (f : ℕ → F) (m : ℕ) (c : Fin s)
    (n : ℕ) :
    ∑ j ∈ range m, resSeq a θ v c n j * f j =
      (v c)⁻¹ * θ ^ (n + 1) * locRes (a c) (n + 1) (vecPoly f m) (wCo a c ^ (n + 1)) := by
  sorry

/-- The diagonal of the scramble (`lem:residue-t0`): `L_c[n][n] = v_c^{-1} θ^{n+1} w_c(a_c)^{-(n+1)}`. -/
theorem resL_diag (a : Fin s → F) (θ : F) (v : Fin s → F) (c : Fin s) (n : ℕ) :
    resL a θ v c n n = (v c)⁻¹ * θ ^ (n + 1) * ((wCo a c).eval (a c))⁻¹ ^ (n + 1) := by
  sorry

/-- **`lem:residue-t0`**: for distinct places, `θ ≠ 0` and a check vector in `(F^*)^s`, the residue
sequence `C_c = L_c P_{a_c}` is a digital `(0,s)`-sequence. -/
theorem resSeq_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q)
    (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) : IsSeq0 D (resSeq a θ v) := by
  sorry

/-- **`lem:residue-rel`** (skeleton relation, general form): for `K ≥ 1` and `deg V < m ≤ sK`,
`∑_c v_c y_{c,K-1}(V) = θ^K [z^{sK-1}] V`. -/
theorem resSeq_skel (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (f : ℕ → F) (m : ℕ) (hm : m ≤ s * K) :
    ∑ c, v c * ∑ j ∈ range m, resSeq a θ v c (K - 1) j * f j =
      θ ^ K * (vecPoly f m).coeff (s * K - 1) := by
  sorry

/-- **`lem:residue-rel`**, first case: `∑_c v_c y_{c,K-1}(V) = 0` for `deg V ≤ sK - 2`. -/
theorem resSeq_skel_zero (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (f : ℕ → F) (m : ℕ)
    (hm : m + 1 ≤ s * K) :
    ∑ c, v c * ∑ j ∈ range m, resSeq a θ v c (K - 1) j * f j = 0 := by
  sorry

/-- **`lem:residue-rel`**, second case: `∑_c v_c y_{c,K-1}(V) = θ^K [z^{sK-1}] V` for `deg V = sK - 1`
(index digits `f_0, …, f_{sK-1}`). -/
theorem resSeq_skel_top (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (f : ℕ → F) :
    ∑ c, v c * ∑ j ∈ range (s * K), resSeq a θ v c (K - 1) j * f j = θ ^ K * f (s * K - 1) := by
  sorry

/-- **`lem:residue-rel`**, "moreover": `∑_c v_c y_{c,K-1+i}(V) = 0` for every `i ≥ 0` and
`deg V ≤ sK - 2`. -/
theorem resSeq_skel_shift (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (i : ℕ) (f : ℕ → F) (m : ℕ)
    (hm : m + 1 ≤ s * K) :
    ∑ c, v c * ∑ j ∈ range m, resSeq a θ v c (K - 1 + i) j * f j = 0 := by
  sorry

/-- The skeleton relation for the points of the digital sequence: for `K ≥ 1` and every index
`x < q^{sK-1}` (the prefix `P_{sK-1}`), `∑_c v_c y_{c,K-1}(x) = 0`. -/
theorem resSeq_skel_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (v : Fin s → F) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hs : 1 ≤ s) (x : ℕ) (hx : x < q ^ (s * K - 1)) :
    ∑ c, v c * seqDigit D (resSeq a θ v) x c (K - 1) = 0 := by
  sorry

end G1

section G2
variable {R : Type*} [CommRing R] {q s : ℕ}

/-- **`lem:prefix`** (separation half, level families): `sep(P_m) ≥ LB ≥ 0` for every `m` of a level
family with largest gap `≤ Δ` gives `δ(P_{[N]}) ≥ LB q^{-Δ/s} N^{-1/s}` for every `N ≥ 2`. -/
theorem prefix_sep_gap (q s : ℕ) (hq : 2 ≤ q) (pt : ℕ → Fin s → ℝ) (Lev : ℕ → Prop) (Δ : ℕ)
    (hgap : HasGap Lev Δ) (LB : ℝ) (hLB : 0 ≤ LB) (h : ∀ m, Lev m → SepAtPrefix q s m pt LB) :
    SepAllN s pt (LB * ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ)))) := by
  sorry

/-- **`lem:prefix`** (mesh ratio, level families): for a `(0,s)`-sequence with `sep(P_m) ≥ LB > 0` for
every `m` of a level family with largest gap `≤ Δ`, `h(P_{[N]}) ≤ √s q^{1+Δ/s}/LB · δ(P_{[N]})` for every
`N ≥ 2` (`h` Euclidean covering radius, `δ = 2 · sepRad` toroidal separation): quasi-uniform. -/
theorem prefix_mesh_gap [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ m, Lev m → SepAtPrefix q s m (seqPoint D C) LB) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q * ((q : ℝ) ^ Δ) ^ (1 / (s : ℝ)) / LB *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C))) := by
  sorry

/-- The level family `sℕ - 1 = {s-1, 2s-1, …}` has largest gap `s` (`rem:prefixcases`; `s ≥ 2`). -/
theorem hasGap_sN1 (hs : 2 ≤ s) : HasGap (fun m => ∃ K, 1 ≤ K ∧ m = s * K - 1) s := by
  sorry

/-- **`rem:prefixcases`**, family `sℕ - 1` (separation): `δ(P_{[N]}) ≥ (LB/q) N^{-1/s}`. -/
theorem prefix_sep_sN1 (q s : ℕ) (hq : 2 ≤ q) (hs : 2 ≤ s) (pt : ℕ → Fin s → ℝ) (LB : ℝ)
    (hLB : 0 ≤ LB) (h : ∀ K, 1 ≤ K → SepAtPrefix q s (s * K - 1) pt LB) :
    SepAllN s pt (LB / q) := by
  sorry

/-- **`rem:prefixcases`**, family `sℕ - 1` (mesh ratio): `h(P_{[N]}) ≤ √s q²/LB · δ(P_{[N]})`. -/
theorem prefix_mesh_sN1 [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K, 1 ≤ K → SepAtPrefix q s (s * K - 1) (seqPoint D C) LB) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * (q : ℝ) ^ 2 / LB *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C))) := by
  sorry

end G2

section G3
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`thm:residue`(i)**: for `K ≥ 1` the fine cells `n̂(x) = (cellIdx x c K)_c` occupied by the points of
`P_{sK-1}` (indices `x < p^{sK-1}`) are exactly the elements of `Λ_v ∩ [0, p^K)^s`, each holding one point. -/
theorem residue_cells (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    (fun x c => cellIdx (zcode p) (resSeq a θ v) x c K) '' Set.Iio (p ^ (s * K - 1)) =
      {n : Fin s → ℕ | (∀ c, n c < p ^ K) ∧ InLat v (fun c => (n c : ℤ))} ∧
    Set.InjOn (fun x c => cellIdx (zcode p) (resSeq a θ v) x c K) (Set.Iio (p ^ (s * K - 1))) := by
  sorry

/-- **`thm:residue`(ii)** (lattice form): if `L ≤ ‖(|b| - 𝟏)_+‖_2` for every nonzero `b ∈ Λ_v`, then any two
distinct points of `P_{sK-1}` have toroidal distance `≥ L · p^{-K}`. -/
theorem residue_sep (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    L ≤ (p : ℝ) ^ K *
      Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq a θ v) x) (seqPoint (zcode p) (resSeq a θ v) y) := by
  sorry

/-- **`thm:residue`(ii)**: any two distinct points of `P_{sK-1}` have toroidal distance
`≥ ℓ_jit(Λ_v) · p^{-K}`. -/
theorem residue_sep_ljit (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    ljit v ≤ (p : ℝ) ^ K *
      Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq a θ v) x) (seqPoint (zcode p) (resSeq a θ v) y) := by
  sorry

/-- **`thm:residue`(ii)** in the paper's normalization: `sep(P_{sK-1}) ≥ p^{-1/s} L` for every `K ≥ 1`. -/
theorem residue_sepAtPrefix (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) (resSeq a θ v))
      ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  sorry

/-- `ℓ_jit(Λ_v) ≥ L` as soon as every nonzero lattice vector has `‖(|b| - 𝟏)_+‖_2 ≥ L`. -/
theorem le_ljit (hs : 1 ≤ s) (v : Fin s → ZMod p) (L : ℝ)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) : L ≤ ljit v := by
  sorry

end G3

section G4
variable {p : ℕ} {s : ℕ}

theorem ljit_le (v : Fin s → ZMod p) (b : Fin s → ℤ) (hb : b ≠ 0) (hlat : InLat v b) :
    ljit v ≤ jitNorm b := by
  sorry

end G4

section G5
variable {p s : ℕ}

theorem korRho_pow_le (hs : 1 ≤ s) : korRho p s ^ s ≤ p := by
  sorry

theorem lt_korRho_succ_pow (hs : 1 ≤ s) : p < (korRho p s + 1) ^ s := by
  sorry

theorem korRho_pow_lt [Fact p.Prime] (hs : 2 ≤ s) : korRho p s ^ s < p := by
  sorry

theorem korRho_two_le_iff [Fact p.Prime] (hs : 2 ≤ s) : 2 ≤ korRho p s ↔ 2 ^ s < p := by
  sorry

theorem korRho_three_le_iff [Fact p.Prime] (hs : 2 ≤ s) : 3 ≤ korRho p s ↔ 3 ^ s < p := by
  sorry

/-- The Korobov vector is a check vector: all entries are nonzero in `𝔽_p`. -/
theorem korobov_ne_zero [Fact p.Prime] (hs : 2 ≤ s) (c : Fin s) : korobov p s c ≠ 0 := by
  sorry

/-- The integer lemma of `cor:korobov`: a vector of `Λ_v` (Korobov `v`) with all `|b_c| ≤ ρ - 1` is `0`. -/
theorem korobov_lat [Fact p.Prime] (hs : 2 ≤ s) (b : Fin s → ℤ) (hlat : InLat (korobov p s) b)
    (hb : ∀ c, |b c| ≤ (korRho p s : ℤ) - 1) : b = 0 := by
  sorry

/-- **`cor:korobov`**: `ℓ_jit(Λ_v) ≥ ρ - 1` for the Korobov vector: every nonzero lattice vector has
`‖(|b| - 𝟏)_+‖_2 ≥ ρ - 1`. -/
theorem korobov_jit [Fact p.Prime] (hs : 2 ≤ s) (b : Fin s → ℤ) (hb : b ≠ 0)
    (hlat : InLat (korobov p s) b) : (korRho p s : ℝ) - 1 ≤ jitNorm b := by
  sorry

theorem korobov_ljit [Fact p.Prime] (hs : 2 ≤ s) : (korRho p s : ℝ) - 1 ≤ ljit (korobov p s) := by
  sorry

/-- **`cor:korobov`**: for the Korobov vector, any two distinct points among the first `N = p^{sK-1}` points
have toroidal distance `≥ (ρ - 1) p^{-1/s} N^{-1/s}`, i.e. `sep(P_{sK-1}) ≥ (ρ - 1) p^{-1/s}`, every `K ≥ 1`. -/
theorem korobov_sep [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ) (hx : x < p ^ (s * K - 1))
    (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) * ((p ^ (s * K - 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / s) ≤
      Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq a θ (korobov p s)) x)
        (seqPoint (zcode p) (resSeq a θ (korobov p s)) y) := by
  sorry

/-- `cor:korobov`, the paper's form `sep(P_{sK-1}) ≥ (ρ - 1) p^{-1/s}` (`SepAtPrefix`). -/
theorem korobov_sepAtPrefix [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p)
    (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) (resSeq a θ (korobov p s)))
      (((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ)))) := by
  sorry

/-- **`cor:korobov`** (comparison forms): for `p > 2^s`,
`(ρ - 1) p^{-1/s} > max(1 - 2p^{-1/s}, (ρ-1)/(ρ+1))` and `> 1/3`; for `p > 3^s` also `> 1/2`. -/
theorem korobov_forms [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    1 - 2 * (p : ℝ) ^ (-(1 : ℝ) / s) < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) ∧
      ((korRho p s : ℝ) - 1) / ((korRho p s : ℝ) + 1) <
        ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) ∧
      1 / 3 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) ∧
      (3 ^ s < p → 1 / 2 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s)) := by
  sorry

/-- **`cor:residueQU`** (separation for every `N`): with `LB = p^{-1/s} L`, `L ≤ ℓ_jit(Λ_v)`,
`δ(P_{[N]}) ≥ (LB/p) N^{-1/s}` for every `N ≥ 2`. -/
theorem residue_allN [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) :
    SepAllN s (seqPoint (zcode p) (resSeq a θ v)) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L / p) := by
  sorry

/-- **`cor:residueQU`** (mesh ratio): with `LB = p^{-1/s} L > 0`, `h(P_{[N]}) ≤ √s p²/LB · δ(P_{[N]})` for
every `N ≥ 2` (`δ = 2 · sepRad`, toroidal): the residue sequence is quasi-uniform. -/
theorem residue_mesh [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (resSeq a θ v))) ≤
      Real.sqrt s * (p : ℝ) ^ 2 / ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
          (prefixSet N (seqPoint (zcode p) (resSeq a θ v)))) := by
  sorry

/-- `cor:residueQU`, converse: for `p < 2^s` every check vector's lattice contains a nonzero
`e ∈ {-1,0,1}^s` (two of the `2^s` subset sums `∑_{c∈A} v_c` agree modulo `p`). -/
theorem small_vec [NeZero p] (hp : p < 2 ^ s) (v : Fin s → ZMod p) :
    ∃ e : Fin s → ℤ, e ≠ 0 ∧ (∀ c, |e c| ≤ 1) ∧ InLat v e := by
  sorry

/-- **`cor:residueQU`**: a check vector with `ℓ_jit(Λ_v) > 0` exists if and only if `p > 2^s` (and then the
Korobov vector is one). -/
theorem jit_exists_iff [Fact p.Prime] (hs : 2 ≤ s) :
    (∃ v : Fin s → ZMod p, (∀ c, v c ≠ 0) ∧ 0 < ljit v) ↔ 2 ^ s < p := by
  sorry

theorem faurePlace_injective (hsp : s ≤ p) : Function.Injective (faurePlace p : Fin s → ZMod p) := by
  sorry

/-- The generator matrices of `𝓡_v` with the Faure places and `θ = 1`:
`C_c[n][i] = v_c^{-1} [t^n] (c + t)^i · w_c(c + t)^{-(n+1)}` (the Palomar statement's `resGen`). -/
theorem resSeq_faure_apply [Fact p.Prime] (v : Fin s → ZMod p) (c : Fin s) (n i : ℕ) :
    resSeq (faurePlace p) 1 v c n i = (v c)⁻¹ * PowerSeries.coeff n
      ((taylor (faurePlace p c) (X ^ i) : PowerSeries (ZMod p)) *
        ((taylor (faurePlace p c) (wCo (faurePlace p) c) : PowerSeries (ZMod p))⁻¹) ^ (n + 1)) := by
  sorry

/-- **`thm:residue` + `cor:korobov` + `cor:residueQU`** for the paper's explicit sequence (Faure places
`a_c = c`, `θ = 1`, Korobov check vector), every `s ≥ 2` and prime `p > 2^s`: a digital `(0,s)`-sequence;
any two distinct points among the first `N = p^{sK-1}` points have toroidal distance
`≥ (ρ - 1) p^{-1/s} N^{-1/s}`; `δ(P_{[N]}) ≥ (LB/p) N^{-1/s}` with `LB = (ρ - 1) p^{-1/s} > 0` for every
`N ≥ 2`; and the mesh ratio is `≤ √s p²/LB` for every `N ≥ 2` (quasi-uniform). -/
theorem residue_korobov [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    IsSeq0 (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ x y : ℕ, x < p ^ (s * K - 1) → y < p ^ (s * K - 1) → x ≠ y →
        ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) *
            ((p ^ (s * K - 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / s) ≤
          Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) x)
            (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) y)) ∧
      0 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) ∧
      SepAllN s (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)))
        (((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) / p) ∧
      (∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)))) ≤
          Real.sqrt s * (p : ℝ) ^ 2 / (((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ)))) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)))))) := by
  sorry

end G5

section G6
variable {s : ℕ}

/-- On `[0,1]^s` the two forms of the toroidal distance agree. -/
theorem torDistR_eq (x y : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hy : ∀ c, 0 ≤ y c ∧ y c ≤ 1) :
    torDistR x y = Z3NetDGS.torDist2 x y := by
  sorry

theorem torDist2_le_euclDist (x y : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1)
    (hy : ∀ c, 0 ≤ y c ∧ y c ≤ 1) : Z3NetDGS.torDist2 x y ≤ euclDist x y := by
  sorry

end G6

section G7
variable {s : ℕ}
variable {R : Type*} [CommRing R] {q : ℕ} [NeZero q]

theorem seqPoint_mem (hq : 2 ≤ q) (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) :
    0 ≤ seqPoint D C v c ∧ seqPoint D C v c ≤ 1 := by
  sorry

/-- `h(P_{[N]}) ≤ √s q N^{-1/s}` with the minimum over indices. -/
theorem covRadIdx_le (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (N : ℕ) (hN : 1 ≤ N) :
    covRadIdx (seqPoint D C) N ≤ Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) := by
  sorry

/-- `δ(P_{[N]}) ≥ b N^{-1/s}` with the minimum over pairs of distinct indices (Euclidean), from the toroidal
`SepAllN`. -/
theorem sepDistIdx_ge (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (b : ℝ)
    (hsep : SepAllN s (seqPoint D C) b) (N : ℕ) (hN : 2 ≤ N) :
    b * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ sepDistIdx (seqPoint D C) N := by
  sorry

/-- `lem:prefix`, "in particular": a `(0,s)`-sequence with `δ(P_{[N]}) ≥ b N^{-1/s}` (`b > 0`, every `N ≥ 2`)
is quasi-uniform, with mesh ratio `≤ √s q / b`. -/
theorem qu_of_sepAllN (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (b : ℝ) (hb : 0 < b) (hsep : SepAllN s (seqPoint D C) b) :
    IsQuasiUniform (seqPoint D C) := by
  sorry

end G7

section G8
variable {s : ℕ}
variable {p : ℕ}

/-- **`cor:residueQU`** (index form): if every nonzero `b ∈ Λ_v` has `‖(|b| - 𝟏)_+‖_2 ≥ L > 0`, the residue
sequence is quasi-uniform. -/
theorem residue_qu [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) :
    IsQuasiUniform (seqPoint (zcode p) (resSeq a θ v)) := by
  sorry

/-- **`thm:residue` + `cor:korobov` + `cor:residueQU`** for the paper's explicit sequence (Faure places, `θ = 1`,
Korobov check vector), in the form of the Palomar statement: for every `s ≥ 2` and prime `p > 2^s`, a digital
`(0,s)`-sequence over `𝔽_p`; for every `K ≥ 1` any two distinct points among the first `N = p^{sK-1}` points
have toroidal distance (written with `round`) at least `(⌊p^{1/s}⌋ - 1) p^{-1/s} N^{-1/s}`; and quasi-uniform. -/
theorem residue_korobov_explicit [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    IsSeq0 (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ v w : ℕ, v < p ^ (s * K - 1) → w < p ^ (s * K - 1) → v ≠ w →
        ((⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) *
            ((p ^ (s * K - 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / s) ≤
          torDistR (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) v)
            (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) w)) ∧
      IsQuasiUniform (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s))) := by
  sorry

end G8

end GeoSeq
