/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V94Defs

@[expose] public section

/-!
# Statements: stage V94 (paper V4)

Staggered residue sequences (`def:residuestar`, `lem:residuestar-t0`, `lem:residuestar-rel`), the one-row certificate and `thm:residuestar`, `cor:dyadic` (value, optimality, `p > 2^s`), the brick wall (`ex:brickwall`, the bridge `def:WF` V4 = V3 multiplier form, `thm:WF` for the V4 definition).
PROVED (`GeoSeq/V94Dyadic.lean`, `GeoSeq/V94Seq.lean`, `GeoSeq/V94Thm.lean`, `GeoSeq/V94WF.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V94`
(definitions in `GeoSeq/V94Defs.lean`). Paper: V4 (`paper/sections/05-residue.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV94.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **`def:residuestar`** (matrix form, uniform): `C_c[n][i] = μ_c θ^N [t^n] (a_c + t)^i U(a_c + t)^{-1}`,
`N = stagLev cs c n`, `U = placeCo a (stagK cs N) c`. -/
theorem resStar_apply (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (n i : ℕ) :
    resStar a θ cs μs k c n i = stagMu cs μs k c * θ ^ stagLev cs c n * PowerSeries.coeff n
      ((taylor (a c) (X ^ i) : PowerSeries F) *
        (taylor (a c) (placeCo a (stagK cs (stagLev cs c n)) c) : PowerSeries F)⁻¹) := by
  sorry

/-- **`def:residuestar`** (matrix form, `c ≠ c⋆`): `C_c[n][i] = μ_c θ^{n+1} [(z - a_c)^n] z^i /
((z - a_{c⋆}) w_c(z)^{n+1})`. -/
theorem resStar_apply_ne (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (hc : c ≠ cs) (n i : ℕ) :
    resStar a θ cs μs k c n i = -μs / k c * θ ^ (n + 1) * PowerSeries.coeff n
      ((taylor (a c) (X ^ i) : PowerSeries F) *
        (taylor (a c) ((X - C (a cs)) * wCo a c ^ (n + 1)) : PowerSeries F)⁻¹) := by
  sorry

/-- **`def:residuestar`** (matrix form, `c = c⋆`): `C_{c⋆}[n][i] = μ⋆ θ^n [(z - a_{c⋆})^n] z^i / w_{c⋆}(z)^n`. -/
theorem resStar_apply_self (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (n i : ℕ) :
    resStar a θ cs μs k cs n i = μs * θ ^ n * PowerSeries.coeff n
      ((taylor (a cs) (X ^ i) : PowerSeries F) *
        (taylor (a cs) (wCo a cs ^ n) : PowerSeries F)⁻¹) := by
  sorry

/-- **`def:residuestar`** (residue reading): digit `n` of coordinate `c` of the point with index digits
`f_0, …, f_{m-1}` is `μ_c θ^N Res_{a_c}(V dz / ((z - a_{c⋆}) w^N))`, `N = stagLev cs c n` (`n + 1` for `c ≠ c⋆`,
`n` for `c⋆`; the pole order at `a_c` is `n + 1`, `stagK_own`). -/
theorem resStar_digit (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (f : ℕ → F)
    (m : ℕ) (c : Fin s) (n : ℕ) :
    ∑ j ∈ range m, resStar a θ cs μs k c n j * f j =
      stagMu cs μs k c * θ ^ stagLev cs c n *
        resAt a (stagK cs (stagLev cs c n)) (vecPoly f m) c := by
  sorry

/-- `lem:residuestar-t0`, the diagonal for `c ≠ c⋆`: `L_c[n][n] = μ_c θ^{n+1} / ((a_c - a_{c⋆}) w'(a_c)^{n+1})`
(`w'(a_c) = w_c(a_c)`). -/
theorem resStarL_diag_ne (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (hc : c ≠ cs) (n : ℕ) :
    resStarL a θ cs μs k c n n =
      -μs / k c * θ ^ (n + 1) / ((a c - a cs) * (wCo a c).eval (a c) ^ (n + 1)) := by
  sorry

/-- `lem:residuestar-t0`, the diagonal for `c⋆`: `L_{c⋆}[n][n] = μ⋆ θ^n / w'(a_{c⋆})^n`. -/
theorem resStarL_diag_self (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (n : ℕ) :
    resStarL a θ cs μs k cs n n = μs * θ ^ n / (wCo a cs).eval (a cs) ^ n := by
  sorry

/-- **`lem:residuestar-t0`**: for distinct places, `θ, μ⋆ ≠ 0` and nonzero weights, the staggered residue
sequence `C_c = L_c P_{a_c}` is a digital `(0,s)`-sequence. -/
theorem resStar_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q)
    (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (cs : Fin s) (μs : F)
    (hμ : μs ≠ 0) (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) :
    IsSeq0 D (resStar a θ cs μs k) := by
  sorry

/-- **`lem:residuestar-rel`**: for `K ≥ 1` and `deg V < m ≤ sK`, `y_{c⋆,K}(V) = ∑_{c ≠ c⋆} k_c y_{c,K-1}(V)`. -/
theorem resStar_rel (a : Fin s → F) (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F)
    (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (f : ℕ → F) (m : ℕ)
    (hm : m ≤ s * K) :
    ∑ j ∈ range m, resStar a θ cs μs k cs K j * f j =
      ∑ c ∈ univ.erase cs, k c * ∑ j ∈ range m, resStar a θ cs μs k c (K - 1) j * f j := by
  sorry

/-- **`lem:residuestar-rel`**, general form: `y_{c⋆,K+i}(V) = ∑_{c ≠ c⋆} k_c y_{c,K-1+i}(V)` for every `i ≥ 0`
and `deg V < m ≤ sK`. -/
theorem resStar_rel_shift (a : Fin s → F) (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F)
    (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : ℕ) (f : ℕ → F) (m : ℕ)
    (hm : m ≤ s * K) :
    ∑ j ∈ range m, resStar a θ cs μs k cs (K + i) j * f j =
      ∑ c ∈ univ.erase cs, k c * ∑ j ∈ range m, resStar a θ cs μs k c (K - 1 + i) j * f j := by
  sorry

/-- `lem:residuestar-rel` for the points of the digital sequence: for `K ≥ 1`, `i ≥ 0` and every index
`x < q^{sK}` (the full level `P_{sK}`), `y_{c⋆,K+i}(x) = ∑_{c ≠ c⋆} k_c y_{c,K-1+i}(x)`. -/
theorem resStar_rel_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : ℕ) (x : ℕ) (hx : x < q ^ (s * K)) :
    seqDigit D (resStar a θ cs μs k) x cs (K + i) =
      ∑ c ∈ univ.erase cs, k c * seqDigit D (resStar a θ cs μs k) x c (K - 1 + i) := by
  sorry

end G0

section G1
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **The carry response of the staggered coordinate** (`lem:residuestar-rel`, prime-base reading): at every
level `K ≥ 1` and carry length `1 ≤ l ≤ K`, the one-digit response `D(l)[c⋆][c']` is `k_{c'}` for `c' ≠ c⋆` and `0`
for `c' = c⋆` (constant responses `X^{(l)}_{c⋆←c'} = k_{c'}`, `O^{(l)}_{c⋆} = 0`). -/
theorem resStar_carry {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hnet : BlockNet0 D (resStar a θ cs μs k) (s * K) 0) (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K)
    (c' : Fin s) :
    IsCarryEntry (resStar a θ cs μs k) K 0 l cs c' (if c' = cs then 0 else k c') := by
  sorry

end G1

section G2
open Finset Polynomial
variable {s : ℕ}

/-- **The one-row certificate** (`lem:cert` with `j = 1`, keeping only the term of one coordinate `c₀`; plan
§2.5): if the prefix `P_{sK}` is a `(0, sK, s)`-net over `ℤ/qℤ` with `q^K ≥ 4`, `Drow l c' = D(l)[c₀][c']` is the
row `c₀` of the one-digit carry response (`1 ≤ l ≤ K`), and `LB ≤ f_1(e_{c₀}, σ_{c₀})` for every step,
`σ_{c₀} = ∑_{c'} e_{c'} D(l_{c'})[c₀][c']`, then `c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_row {q : ℕ} [NeZero q] (C : Gen s (ZMod q)) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (c₀ : Fin s) (Drow : ℕ → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c', IsCarryEntry C K 0 l c₀ c' (Drow l c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ (gapNum1 q (e c₀) (∑ c', (e c' : ZMod q) * Drow (l c') c') : ℝ) / q) :
    SepAtLevel q s K (seqPoint (zcode q) C) (min 1 LB) := by
  sorry

end G2

section G3
open Finset Polynomial
variable {s : ℕ}
variable {p : ℕ} [Fact p.Prime]

/-- **`thm:residuestar`** (separation): for a prime `p ≥ 5`, distinct places, `θ, μ⋆ ≠ 0` and nonzero weights,
`sep(P_{sK}) ≥ β(k)` for every `K ≥ 1`. -/
theorem residuestar_sep (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p s K (seqPoint (zcode p) (resStar a θ cs μs k)) (betaStar p cs k) := by
  sorry

/-- **`thm:residuestar`** (all `N`): if `β(k) ≥ 0`, then `δ(P_{[N]}) ≥ (β(k)/p) N^{-1/s}` for every `N ≥ 2`. -/
theorem residuestar_allN (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (hβ : 0 ≤ betaStar p cs k) :
    SepAllN s (seqPoint (zcode p) (resStar a θ cs μs k)) (betaStar p cs k / p) := by
  sorry

/-- **`thm:residuestar`** (mesh ratio): if `β(k) > 0`, then `h(P_{[N]}) ≤ (√s p / β(k)) δ(P_{[N]})` for every
`N ≥ 2` (`δ` toroidal, `2 · sepRad`). -/
theorem residuestar_mesh (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (hβ : 0 < betaStar p cs k) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (resStar a θ cs μs k))) ≤
      Real.sqrt s * p / betaStar p cs k *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
          (prefixSet N (seqPoint (zcode p) (resStar a θ cs μs k)))) := by
  sorry

/-- **`thm:residuestar`** (quasi-uniformity): if `β(k) > 0`, the staggered residue sequence is quasi-uniform. -/
theorem residuestar_qu (hp : 5 ≤ p) (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (k : Fin s → ZMod p)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (hβ : 0 < betaStar p cs k) :
    IsQuasiUniform (seqPoint (zcode p) (resStar a θ cs μs k)) := by
  sorry

end G3

section G4
open Finset Polynomial
variable {s : ℕ}

/-- A signed sum of distinct powers of two is nonzero: if `e ∈ {-1,0,1}^s` is not `0` and `o` is injective on
its support, then `∑_c e_c 2^{o(c)} ≠ 0` (the term of the smallest exponent is not divisible by the next power). -/
theorem signed_pow_two_ne_zero (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0)
    (o : Fin s → ℕ) (ho : ∀ c c', e c ≠ 0 → e c' ≠ 0 → o c = o c' → c = c') :
    ∑ c, e c * 2 ^ o c ≠ 0 := by
  sorry

/-- `|∑_c e_c 2^{o(c)}| ≤ 2^{s-1} - 1` when `o` is injective with values `< s - 1` on the support of `e`. -/
theorem abs_signed_pow_two_lt (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (o : Fin s → ℕ)
    (ho : ∀ c c', e c ≠ 0 → e c' ≠ 0 → o c = o c' → c = c') (hlt : ∀ c, e c ≠ 0 → o c < s - 1) :
    |∑ c, e c * 2 ^ o c| < 2 ^ (s - 1) := by
  sorry

/-- **The dyadic estimate** (proof of `cor:dyadic`, first part): if `2^{s-1} x = A` in `ℤ/pℤ` for an integer `A`
with `0 < |A| < 2^{s-1}`, then `|x|_∘ ≥ ⌊p/2^{s-1}⌋`. -/
theorem cabsZ_ge_of_mul {p : ℕ} [NeZero p] (M : ℕ) (x : ZMod p) (A : ℤ) (hA0 : A ≠ 0)
    (hAM : |A| < M) (hx : (M : ZMod p) * x = A) : p / M ≤ cabsZ x := by
  sorry

end G4

section G5
open Finset Polynomial
variable {s : ℕ}
variable {p : ℕ} [NeZero p]

/-- **Pigeonhole on the cycle** (`cor:dyadic`, second part): for every weights `k ∈ (ℤ/pℤ)^s` some step `e'`
(`e'_{c⋆} = 0`, `e' ∈ {-1,0,1}^s \ {0}`) has `|k · e'|_∘ ≤ ⌊p/2^{s-1}⌋`: otherwise the `2^{s-1}` subset sums
`S_A = ∑_{c ∈ A} k_c` (`A ⊆ C`) would carry pairwise disjoint arcs of `⌊p/2^{s-1}⌋ + 1` points. -/
theorem exists_small_step (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) :
    ∃ e, StarStep cs e ∧ cabsZ (∑ c, (e c : ZMod p) * k c) ≤ p / 2 ^ (s - 1) := by
  sorry

end G5

section G6
open Finset Polynomial
variable {s : ℕ}
variable {p : ℕ} [Fact p.Prime]

/-- **`cor:dyadic`**, lower bound: for an odd prime `p`, every step `e'` has `|k · e'|_∘ ≥ ⌊p/2^{s-1}⌋` for the
dyadic weights `k_c = 2^{o(c)}/2^{s-1}` (`o` injective on `C` with values `< s - 1`). -/
theorem cabsZ_dyadic (hp2 : p ≠ 2) (cs : Fin s) (o : Fin s → ℕ)
    (ho : ∀ c c', c ≠ cs → c' ≠ cs → o c = o c' → c = c') (hlt : ∀ c, c ≠ cs → o c < s - 1)
    (e : Fin s → ℤ) (he : StarStep cs e) :
    p / 2 ^ (s - 1) ≤ cabsZ (∑ c, (e c : ZMod p) * dyadicK p o c) := by
  sorry

/-- **`cor:dyadic`** (optimality): for every weights `k`, `β(k) ≤ (⌊p/2^{s-1}⌋ - 1)/p`. -/
theorem betaStar_le_dyadic (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) :
    betaStar p cs k ≤ (((p / 2 ^ (s - 1) : ℕ) : ℝ) - 1) / p := by
  sorry

/-- **`cor:dyadic`** (value): for an odd prime `p` and an admissible order `o`,
`β(dyadic) = (⌊p/2^{s-1}⌋ - 1)/p`. -/
theorem betaStar_dyadic (hp2 : p ≠ 2) (hs : 2 ≤ s) (cs : Fin s) (o : Fin s → ℕ)
    (ho : ∀ c c', c ≠ cs → c' ≠ cs → o c = o c' → c = c') (hlt : ∀ c, c ≠ cs → o c < s - 1) :
    betaStar p cs (dyadicK p o) = (((p / 2 ^ (s - 1) : ℕ) : ℝ) - 1) / p := by
  sorry

/-- **`cor:dyadic`** ("only if"): if `β(k) > 0` for some weights `k`, then `p > 2^s`. -/
theorem betaStar_pos_imp (hs : 2 ≤ s) (cs : Fin s) (k : Fin s → ZMod p) (hβ : 0 < betaStar p cs k) :
    2 ^ s < p := by
  sorry

/-- The standard order is admissible: injective on `C` with values `< s - 1`. -/
theorem stdOrder_inj (cs : Fin s) (c c' : Fin s) (hc : c ≠ cs) (hc' : c' ≠ cs)
    (h : stdOrder cs c = stdOrder cs c') : c = c' := by
  sorry

theorem stdOrder_lt (cs : Fin s) (c : Fin s) (hc : c ≠ cs) : stdOrder cs c < s - 1 := by
  sorry

/-- **`cor:dyadic`** ("in particular"): for every `s ≥ 2` and every prime `p > 2^s`, the staggered residue sequence
with dyadic weights (any admissible order, distinct places, `θ, μ⋆ ≠ 0`) is a digital `(0,s)`-sequence with
`sep(P_{sK}) ≥ (⌊p/2^{s-1}⌋ - 1)/p` for every `K ≥ 1`, and it is quasi-uniform. -/
theorem dyadic_qu (hs : 2 ≤ s) (hps : 2 ^ s < p) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (cs : Fin s) (μs : ZMod p) (hμ : μs ≠ 0) (o : Fin s → ℕ)
    (ho : ∀ c c', c ≠ cs → c' ≠ cs → o c = o c' → c = c') (hlt : ∀ c, c ≠ cs → o c < s - 1) :
    IsSeq0 (zcode p) (resStar a θ cs μs (dyadicK p o)) ∧
      (∀ K, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (resStar a θ cs μs (dyadicK p o)))
        ((((p / 2 ^ (s - 1) : ℕ) : ℝ) - 1) / p)) ∧
      IsQuasiUniform (seqPoint (zcode p) (resStar a θ cs μs (dyadicK p o))) := by
  sorry

end G6

section G7
open Finset PowerSeries
open scoped Polynomial
variable {F : Type*} [Field F]

/-- **The brick-wall family in the multiplier form** (`lem:resform`(b) for `s = 2`, `c⋆ = 1`, Faure places):
`𝓡^⋆ = ssGen g zθ` with `zθ_c = z_c(θx)`, `g_0 = μ_0 θ u_0(θx)`, `g_1 = μ⋆ u_1(θx) z_1(θx)²`. -/
theorem resStar_faure_ss (θ μs : F) (k : Fin 2 → F) :
    resStar faurePl θ 1 μs k =
      ssGen ![C (stagMu 1 μs k 0 * θ) * rescale θ (uF 0),
          C μs * rescale θ (uF 1) * rescale θ (zF 1) ^ 2]
        (fun c => rescale θ (zF c)) := by
  sorry

/-- The weight of the staggered coordinate does not enter `𝓡^⋆_v`. -/
theorem resStar_congr {s : ℕ} (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k k' : Fin s → F)
    (h : ∀ c, c ≠ cs → k c = k' c) : resStar a θ cs μs k = resStar a θ cs μs k' := by
  sorry

end G7

section G8
open Finset PowerSeries
open scoped Polynomial
variable {F : Type*} [Field F]
local notation "PS" => PowerSeries F
variable (h2 : (2 : F) ≠ 0) (ρ : PowerSeries F) (hρ : ρ ^ 2 = 1 + C (-1) * X) (hρ0 : constantCoeff ρ = 1)
include h2 hρ hρ0

/-- The brick-wall family over a field of characteristic `≠ 2`: the staggered residue sequence of `ex:brickwall`
is `ssGen g zθ` with `g = (2ρ/((1-x)(1+ρ)), (1+ρ)/ρ)` and `zθ = ((1-ρ)/2, (1+ρ)/2)`, `ρ = √(1 - x)`. -/
theorem brick_ss :
    resStar faurePl (-(4 : F)⁻¹) 1 2 ![(2 : F)⁻¹, 0] =
      ssGen ![C (2 : F) * ρ * ((1 - X : PS) * (1 + ρ))⁻¹, (1 + ρ) * ρ⁻¹]
        ![C (2 : F)⁻¹ * (1 - ρ), C (2 : F)⁻¹ * (1 + ρ)] := by
  sorry

end G8

section G9
open Finset PowerSeries
open scoped Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- **The bridge** (`def:WF`, every prime `p ≥ 3`): the V4 brick wall (the staggered residue sequence of
`ex:brickwall`) is the V3 multiplier form `WFgen p (-1)` of `W^-`. -/
theorem brickWall_eq_WFgen (hp : 3 ≤ p) : brickWall p = WFgen p (-1) := by
  sorry

/-- **`ex:brickwall`** (`p = 7`): the leading `4 × 4` block of `C_0` of the V4 brick wall is that of
`ex:running`. -/
theorem brickWall_C0 :
    (Matrix.of fun n k : Fin 4 => brickWall 7 0 n k) = !![1, 0, 0, 0; 6, 2, 0, 0; 5, 2, 4, 0; 0, 1, 5, 1] := by
  sorry

/-- **`ex:brickwall`** (`p = 7`): the leading `4 × 4` block of `C_1` of the V4 brick wall is that of
`ex:running`. -/
theorem brickWall_C1 :
    (Matrix.of fun n k : Fin 4 => brickWall 7 1 n k) = !![2, 2, 2, 2; 4, 0, 3, 6; 3, 1, 0, 0; 6, 1, 2, 0] := by
  sorry

/-- **`thm:WF`** (V4 definition; proof via `cor:dyadic` with `s = 2`): for every prime `p ≥ 5` the brick wall is a
digital `(0,2)`-sequence with `sep(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`, and it is quasi-uniform. -/
theorem brickWall_WF (hp : 5 ≤ p) :
    IsSeq0 (zcode p) (brickWall p) ∧
      (∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (brickWall p)) (((p : ℝ) - 3) / (2 * p))) ∧
      IsQuasiUniform (seqPoint (zcode p) (brickWall p)) := by
  sorry

end G9

end GeoSeq
