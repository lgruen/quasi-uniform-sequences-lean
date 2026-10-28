/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7Defs
public import GeoSeq.V3Defs
public import GeoSeq.S3Defs
public import GeoSeq.F4
public import GeoSeq.K4Defs
public import GeoSeq.S4Defs
public import Z3Net.DGSDefs

@[expose] public section

/-!
# Statements: stage V7 (`app:p7`, `lem:shift`, `thm:B2`, `sec:dims`)

The graph rule (`def:graphrule`, realizability) and `thm:p7` (base seven, kernel-checked graph certificate), digital shifts (`lem:shift`), the `κ_m` side claim of `thm:B2`, and the assembly theorems `thm:dim3`, `thm:dim45`.
PROVED (`GeoSeq/V7Graph.lean`, `V7P7Data.lean`, `V7P7a/b/c.lean`, `V7P7.lean`, `V7Shift.lean`, `V7B2.lean`,
`V7Dim.lean`, `V7Dim45.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v7_statements.py`
(definitions in `GeoSeq/V7Defs.lean`). Paper: V3 (development version V3 of the paper, `B-p7.tex`, `09-practice.tex`,
`08-frames.tex`, `07-dims.tex`); label → Lean map in the formalization notes of the research repository, review
the statement-review notes of the research repository. Configurations: `comparatorGeoSeqV7.json`, `comparatorGeoSeqV7d45.json`
(the assembly modulo the small-base certificates `thm:S3`, `thm:K4`, `thm:S4`, which have their own configurations),
`comparatorGeoSeqV7full.json` (`dim3`, `dim45_q4`, `dim45` unconditional).
-/

namespace GeoSeq
open Finset PowerSeries
open scoped Polynomial

section G0
variable {F : Type*} [Field F]

/-- **Realizability of the graph rule** (the paragraph before `def:graphrule`, from `prop:depthdir`): for `θ ≠ 0`,
at every depth `l`, column `c'` and history `h`, the digit `ψ` gives the own response the prescribed value
`w(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})` if and only if `ψ` is the graph rule's digit. -/
theorem graphRule_unique (wt : F → F → F) (θ : F) (hθ : θ ≠ 0) (lamv : Fin 3 → F)
    (zθ : Fin 3 → PowerSeries F) (c' : Fin 3) (h : ℕ → F) (l : ℕ) (ψ : F) :
    (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c' =
        wt (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2 ↔
      ψ = graphRule wt θ lamv zθ c' l h := by
  sorry

end G0

section G1
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The responses of the graph-rule scramble lie on the graph** (`def:graphrule`): for every column `c'`, every
level `K` and every carry length `1 ≤ l ≤ K`, the own response is `O^{(l)}_{c'} = w(X^{(l)}_{c'+1←c'},
X^{(l)}_{c'+2←c'})`. -/
theorem graph_resp (wt : F → F → F) (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = 3) (θ : F)
    (hθ : θ ≠ 0) (zθ : Fin 3 → PowerSeries F) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin 3 → F) (hlam : ∀ c, lamv c ≠ 0)
    (c' : Fin 3) (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (d0 d1 d2 : F)
    (h0 : IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l c' c' d0)
    (h1 : IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 1) c' d1)
    (h2 : IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 2) c' d2) :
    d0 = wt d1 d2 := by
  sorry

end G1

section G2

/-- `σ_c(-e) = -σ_c(e)`. -/
theorem graphSig_neg {p : ℕ} (wt : ZMod p → ZMod p → ZMod p) (e : Fin 3 → ℤ)
    (ξ : Fin 3 → ZMod p × ZMod p) (c : Fin 3) : graphSig wt (-e) ξ c = -graphSig wt e ξ c := by
  sorry

/-- **`LB^{act}_K ≥ LB(w)`** (proof of `thm:p7`): if every column of every `D(l)` (`1 ≤ l ≤ K`) of a
`(0,3)`-sequence over `𝔽_p` (`p ≥ 5`) lies on the graph of `w` and `LB ≤ LB(w)`, then every term of the
certificate `LB^{act}_K` (`lem:cert`, `j = 1`) is `≥ LB`, and `c(P_{3K}) ≥ min(1, LB)`. -/
theorem graph_cert (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (wt : ZMod p → ZMod p → ZMod p)
    (C : Gen 3 (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (hG : ∀ K l, 1 ≤ l → l ≤ K → ∀ c' (d0 d1 d2 : ZMod p), IsCarryEntry C K 0 l c' c' d0 →
      IsCarryEntry C K 0 l (c' + 1) c' d1 → IsCarryEntry C K 0 l (c' + 2) c' d2 → d0 = wt d1 d2)
    (LB : ℝ) (hLB : GraphLB p wt LB) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ∀ d : Fin 3 → Fin 3 → ZMod p,
      (∀ c c', IsCarryEntry C K 0 (l c') c c' (d c c')) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2)) ∧
    SepAtLevel p 3 K (seqPoint (zcode p) C) (min 1 LB) := by
  sorry

/-- **The graph rule** (`def:graphrule`, the text after it, and the proof of `thm:p7` for any table): let `p ≥ 5` be
prime, `w : 𝔽_p^2 → 𝔽_p` any table, and take any frame of three distinct places (`w` monic of degree `3`, local roots
`z_c(θx)` with `w(z_c(θx)) = θx`), any scale `θ ≠ 0` and any constants `λ_c ≠ 0`. Then
(a) at every depth `l ≥ 1` and for every history there is exactly one digit with
`O^{(l)}_{c'} = w(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})`, the graph rule's;
(b) the graph rule defines a self-similar scramble with the constants `λ_c` (free series = the chosen digits) and a
digital `(0,3)`-sequence over `𝔽_p`;
(c) every column of every `D(l)` lies on the graph `{(w(ξ); ξ)}`;
(d) for every `LB ≤ LB(w)` and every `K ≥ 1`, every term of `LB^{act}_K` is `≥ LB` and `c(P_{3K}) ≥ min(1, LB)`. -/
theorem graph_seq (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (wt : ZMod p → ZMod p → ZMod p)
    (w : (ZMod p)[X]) (hw : w.Monic) (hdeg : w.natDegree = 3) (θ : ZMod p) (hθ : θ ≠ 0)
    (zθ : Fin 3 → PowerSeries (ZMod p)) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin 3 → ZMod p) (hlam : ∀ c, lamv c ≠ 0) :
    (∀ c' (h : ℕ → ZMod p) (l : ℕ), ∃! ψ : ZMod p,
      (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c' =
        wt (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2) ∧
    (∀ c, constantCoeff (ruleMult θ lamv zθ (graphRule wt θ lamv zθ) c) ≠ 0 ∧
      lam (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ c = lamv c ∧
      freeSer (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ c =
        rescale θ (PowerSeries.mk (ruleDigit (graphRule wt θ lamv zθ) c))) ∧
    IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) ∧
    (∀ K l, 1 ≤ l → l ≤ K → ∀ c' (d0 d1 d2 : ZMod p),
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l c' c' d0 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 1) c' d1 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 l (c' + 2) c' d2 →
      d0 = wt d1 d2) ∧
    ∀ LB : ℝ, GraphLB p wt LB → ∀ K : ℕ, 1 ≤ K →
      (∀ e l, IsStep K e l → ∀ d : Fin 3 → Fin 3 → ZMod p,
        (∀ c c', IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ) K 0 (l c') c c'
          (d c c')) →
        LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * d c c') : ℝ) / p) ^ 2)) ∧
      SepAtLevel p 3 K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ (graphRule wt θ lamv zθ)) zθ))
        (min 1 LB) := by
  sorry

end G2

section G3

/-- **Soundness of the checker**: if `p7chk` accepts the codes of a step `e ∈ {-1,0,1}^3`, then for every choice of
`ξ^{(c')} ∈ 𝔽_7^2` some coordinate has `f_1(e_c, σ_c) ≠ 0`. -/
theorem p7chk_sound (e : Fin 3 → ℤ) (he : ∀ c, e c = -1 ∨ e c = 0 ∨ e c = 1)
    (hchk : p7chk (p7code (e 0)) (p7code (e 1)) (p7code (e 2)) = true)
    (ξ : Fin 3 → ZMod 7 × ZMod 7) : ∃ c, gapNum1 7 (e c) (graphSig wP7 e ξ c) ≠ 0 := by
  sorry

end G3

section G4

/-- `thm:p7`, step `(1, 1, 1)`: no vanishing combination (`7^6` combinations). -/
theorem p7chk_111 : p7chk 1 1 1 = true := by
  sorry

/-- `thm:p7`, step `(1, 1, -1)`: no vanishing combination (`7^6` combinations). -/
theorem p7chk_116 : p7chk 1 1 6 = true := by
  sorry

end G4

section G5

/-- `thm:p7`, step `(1, -1, 1)`: no vanishing combination (`7^6` combinations). -/
theorem p7chk_161 : p7chk 1 6 1 = true := by
  sorry

/-- `thm:p7`, step `(1, -1, -1)`: no vanishing combination (`7^6` combinations). -/
theorem p7chk_166 : p7chk 1 6 6 = true := by
  sorry

end G5

section G6

/-- `thm:p7`, the nine steps with one or two moving coordinates whose first nonzero entry is `+1`. -/
theorem p7chk_small : p7chk 1 1 0 = true ∧ p7chk 1 6 0 = true ∧ p7chk 1 0 1 = true ∧ p7chk 1 0 6 = true ∧
    p7chk 0 1 1 = true ∧ p7chk 0 1 6 = true ∧ p7chk 1 0 0 = true ∧ p7chk 0 1 0 = true ∧
    p7chk 0 0 1 = true := by
  sorry

end G6

section G7

/-- **`LB(w) ≥ 1/7`** for the table `w` of `tab:p7` (the finite statement of the proof of `thm:p7`: no step and no
choice of the `ξ^{(c')}` makes every term vanish). -/
theorem p7_LB : GraphLB 7 wP7 (1 / 7) := by
  sorry

/-- **`LB(w) = 1/7`** (proof of `thm:p7`): `1/7` is the largest `LB` with `LB ≤ LB(w)`; it is attained by the axis
step `e = (1, 0, 0)` with `ξ = (0, 1)`. -/
theorem p7_LB_eq : IsGreatest {LB : ℝ | GraphLB 7 wP7 LB} (1 / 7) := by
  sorry

/-- **`thm:p7`** (base seven). Let `w` be the table of `tab:p7`. For every frame of three distinct places in `𝔽_7`
(`w` monic of degree `3`, local roots `z_c(θx)` with `w(z_c(θx)) = θx`), every scale `θ ≠ 0` and all constants
`λ_c ≠ 0`: the graph rule is well defined (at every depth and history exactly one digit puts the own response on the
graph), it defines a self-similar scramble with the constants `λ_c`, all responses lie on the graph, and the sequence
is a quasi-uniform digital `(0,3)`-sequence over `𝔽_7` with `c(P_{3K}) ≥ 1/7` for every `K ≥ 1` (mesh ratio
`≤ √3 · 7 / (1/7)` along all `N ≥ 2`, `lem:prefix`). -/
theorem p7 (w : (ZMod 7)[X]) (hw : w.Monic) (hdeg : w.natDegree = 3) (θ : ZMod 7) (hθ : θ ≠ 0)
    (zθ : Fin 3 → PowerSeries (ZMod 7)) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (lamv : Fin 3 → ZMod 7) (hlam : ∀ c, lamv c ≠ 0) :
    (∀ c' (h : ℕ → ZMod 7) (l : ℕ), ∃! ψ : ZMod 7,
      (stBeta θ lamv zθ c' h l - (θ ^ l * ψ) • stAlpha θ lamv zθ c') c' =
        wP7 (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2) ∧
    (∀ c, constantCoeff (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ) c) ≠ 0 ∧
      lam (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ c = lamv c) ∧
    (∀ K l, 1 ≤ l → l ≤ K → ∀ c' (d0 d1 d2 : ZMod 7),
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) K 0 l c' c' d0 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) K 0 l (c' + 1) c' d1 →
      IsCarryEntry (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) K 0 l (c' + 2) c' d2 →
      d0 = wP7 d1 d2) ∧
    QUSep (zcode 7) 3 (ssGen (ruleMult θ lamv zθ (graphRule wP7 θ lamv zθ)) zθ) (1 / 7) := by
  sorry

/-- Non-vacuity of `thm:p7`: on the Faure frame `z(z-1)(z-2)` (`θ = 1`, `λ = 1`) the graph rule of `tab:p7` gives a
quasi-uniform digital `(0,3)`-sequence over `𝔽_7` with `c(P_{3K}) ≥ 1/7` for every `K ≥ 1`. -/
theorem p7_exists : ∃ C : Gen 3 (ZMod 7), QUSep (zcode 7) 3 C (1 / 7) := by
  sorry

end G7

section G8
variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **`lem:shift`, `t = 0`**: the shifted sequence (digits `y_{c,n}(v) + ς_{c,n}`, any array `ς`) is a
`(0,s)`-sequence if and only if the unshifted one is. -/
theorem shift_seq0 (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) :
    IsSeq0Sh D C ς ↔ IsSeq0 D C := by
  sorry

/-- **`lem:shift`, the certificate** (any digit code `D`, any array `ς` of digits): under the hypotheses of
`lem:cert` (`cert`: `P_{sK}` a `(0,sK,s)`-net, `q^K ≥ 4`, carry responses `D_i(l)`, `LB` at most every certificate
term), the SHIFTED prefix `P_{sK}` has `c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_shift [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R)
    (K j : ℕ)
    (hK : 4 ≤ q ^ K) (hnet : BlockNet0 D C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → R)
    (hD0 : ∀ i c c', Dr i 0 c c' = 0)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ)
    (hLB : ∀ e l, IsStep K e l → ∀ y : Fin s → R, LB ≤ certTerm D j e (certSigma D Dr j e l y)) :
    SepAtLevel q s K (shPoint D C ς) (min 1 LB) := by
  sorry

end G8

section G9
variable {s q : ℕ}
variable {R : Type*} [CommRing R] [NeZero q]

/-- **`lem:shift`, "in particular"**: let `(y(v))` be a digital `(0,s)`-sequence over the digit code `D`, `ς` any
array of digits, and suppose `lem:cert` gives `c(P_{sK}) ≥ LB` (`0 < LB ≤ 1`) for every `K` with `q^K ≥ 4`
(`CertAt`). Let `q^{K_0} ≥ 4`. Then the shifted sequence is a `(0,s)`-sequence, `c(P_{sK}) ≥ LB` for its full levels
with `q^K ≥ 4`, and for every `N > q^{s(K_0-1)}` the bounds of `lem:prefix` hold for it:
`δ(P_{[N]}) ≥ (LB/q) N^{-1/s}` (any two distinct points among the first `N`), `h(P_{[N]}) ≤ √s q N^{-1/s}` and
`h(P_{[N]}) ≤ (√s q/LB) · δ(P_{[N]})` (`h` Euclidean covering radius, `δ = 2 · sepRad` toroidal). -/
theorem shift_prefix [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R)
    (hq : 2 ≤ q) (hs : 1 ≤ s) (hseq : IsSeq0 D C) (LB : ℝ) (hLB0 : 0 < LB) (hLB1 : LB ≤ 1)
    (hcert : ∀ K : ℕ, 4 ≤ q ^ K → CertAt D C K LB) (K0 : ℕ) (hK0 : 4 ≤ q ^ K0) :
    IsSeq0Sh D C ς ∧ (∀ K : ℕ, 4 ≤ q ^ K → SepAtLevel q s K (shPoint D C ς) LB) ∧
    ∀ N : ℕ, q ^ (s * (K0 - 1)) < N →
      (∀ v w : ℕ, v < N → w < N → v ≠ w →
        LB / q * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ Z3NetDGS.torDist2 (shPoint D C ς v) (shPoint D C ς w)) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q / LB * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (shPoint D C ς))) := by
  sorry

/-- **`lem:shift`, "for `q ≥ 4` this is every `N ≥ 2`"**: the bounds of `lem:prefix` hold for the shifted sequence
for every `N ≥ 2` (`K_0 = 1`). -/
theorem shift_prefix_q4 [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R)
    (ς : Fin s → ℕ → R) (hq : 4 ≤ q) (hs : 1 ≤ s) (hseq : IsSeq0 D C) (LB : ℝ) (hLB0 : 0 < LB)
    (hLB1 : LB ≤ 1) (hcert : ∀ K : ℕ, 1 ≤ K → CertAt D C K LB) (N : ℕ) (hN : 2 ≤ N) :
    (∀ v w : ℕ, v < N → w < N → v ≠ w →
        LB / q * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ Z3NetDGS.torDist2 (shPoint D C ς v) (shPoint D C ς w)) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q / LB * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (shPoint D C ς))) := by
  sorry

end G9

section G10

/-- **`thm:B2`, `κ_m`-separation**: for every `m`, the prefix `P_m` (the first `2^m` points) of the sequence of
`thm:B2` is `κ_m`-separated and toroidally `κ_m`-separated in base `2` in the sense of [DGS2], `κ_m = ⌈m/2⌉ + 3`
(`⌈m/2⌉ = (m+1)/2` in `ℕ`). -/
theorem B2_kappa (m : ℕ) :
    Z3NetDGS.IsKSep 2 ((m + 1) / 2 + 3) (prefixSet (2 ^ m) (seqPoint (zcode 2) B2gen)) ∧
      Z3NetDGS.IsKSepTor 2 ((m + 1) / 2 + 3) (prefixSet (2 ^ m) (seqPoint (zcode 2) B2gen)) := by
  sorry

end G10

section G11

/-- **`tab:dim3`, the prime bases**: `p = 7` (graph rule, `thm:p7`: `1/7`); `p = 11` (`thm:LF`(b): `1/11`); every prime
`p ≥ 13` (archived ordered designs or the mixed-radix rule, `thm:LF`(a): `(p - Γ)/p > 0.1`, and `≥ 0.3` from `31`);
every prime `p ≥ 41` (mixed-radix rule, `thm:MRall`, `tab:P1`: `Γ < p`, and `(p-Γ)/p ≥ 1 - 3.99 p^{-1/3}` from
`67`); every prime `p ≥ 1.97·10^7` (staggered rule, `thm:A3`: `1 - 742/p`). Each: a quasi-uniform digital
`(0,3)`-sequence over `𝔽_p` with the bound on `c(P_{3K})` for every `K ≥ 1`. -/
theorem dim3_primes :
    (∃ C : Gen 3 (ZMod 7), QUSep (zcode 7) 3 C (1 / 7)) ∧
    (∃ C : Gen 3 (ZMod 11), QUSep (zcode 11) 3 C (1 / 11)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 13 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p ∧
      (31 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - Γ) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 41 ≤ p → mrCost 3 p (mrRuleH 3 p) < p ∧
      (67 ≤ p → 1 - 399 / 100 * (p : ℝ) ^ (-(1 : ℝ) / 3) ≤ ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 19700000 ≤ p → ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (1 - 742 / p)) := by
  sorry

/-- **`thm:dim3`, the primes**: every prime `p ≥ 7` has a quasi-uniform digital `(0,3)`-sequence over `𝔽_p` with a
positive lower bound `LB` on `c(P_{3K})` for every `K ≥ 1`: `LB = 1/7` at `p = 7`, `1/11` at `p = 11`, `LB > 0.1`
from `13` on (`tab:dim3`). -/
theorem dim3_every_prime (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) :
    ∃ LB : ℝ, 0 < LB ∧ (p = 7 → LB = 1 / 7) ∧ (p = 11 → LB = 1 / 11) ∧ (13 ≤ p → 1 / 10 < LB) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C LB := by
  sorry

/-- **`thm:dim3` from the small-base theorems** (`tab:dim3`): given the statements of `thm:S3` (`S3_net`, `S3_sep`)
and `thm:K4` (`K4_net`, `K4_sep`): for `q = 3` (the sequence `S3gen` of `thm:S3`, `c(P_{3K}) ≥ 0.05598`), `q = 4`
(the sequence `K4gen` of `thm:K4`, `≥ 0.11293`) and every prime
`p ≥ 7` there is a quasi-uniform digital `(0,3)`-sequence over `𝔽_q` with an explicit positive lower bound on
`c(P_{3K})` for every `K ≥ 1`, with the rows of `tab:dim3` (`dim3_primes`). -/
theorem dim3_of_small (hS3n : IsSeq0 (zcode 3) S3gen)
    (hS3s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 3 3 K (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561))
    (hK4n : IsSeq0 f4code K4gen)
    (hK4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 3 K (seqPoint f4code K4gen) (Real.sqrt 54774953 / 65536)) :
    QUSep (zcode 3) 3 S3gen (5598 / 100000) ∧ QUSep f4code 3 K4gen (11293 / 100000) ∧
    (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ LB : ℝ, 0 < LB ∧ (p = 7 → LB = 1 / 7) ∧ (p = 11 → LB = 1 / 11) ∧
      (13 ≤ p → 1 / 10 < LB) ∧ ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C LB) ∧
    (∀ (p : ℕ) [Fact p.Prime], 41 ≤ p → mrCost 3 p (mrRuleH 3 p) < p ∧
      (67 ≤ p → 1 - 399 / 100 * (p : ℝ) ^ (-(1 : ℝ) / 3) ≤ ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 19700000 ≤ p → ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (1 - 742 / p)) := by
  sorry

/-- **`thm:dim3`** (dimension three; `tab:dim3`): for `q = 3`, `q = 4` and every prime `p ≥ 7` there is a quasi-uniform
digital `(0,3)`-sequence over `𝔽_q` with an explicit positive lower bound on `c(P_{3K})` for every `K ≥ 1`:
`0.05598` (`q = 3`, the Artin–Schreier sequence `S3gen` of `thm:S3`), `0.11293` (`q = 4`, the Kummer sequence `K4gen`
over `𝔽_4` of `thm:K4`),
`1/7` (`p = 7`, graph rule, `thm:p7`), `1/11` (`p = 11`, `thm:LF`(b)), `(p-Γ)/p > 0.1` (every prime `p ≥ 13`,
`thm:LF`(a)); and the further rows: mixed-radix rule from `41` (`1 - 3.99 p^{-1/3}` from `67`), staggered rule from
`1.97·10^7` (`1 - 742/p`). -/
theorem dim3 :
    QUSep (zcode 3) 3 S3gen (5598 / 100000) ∧ QUSep f4code 3 K4gen (11293 / 100000) ∧
    (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ LB : ℝ, 0 < LB ∧ (p = 7 → LB = 1 / 7) ∧ (p = 11 → LB = 1 / 11) ∧
      (13 ≤ p → 1 / 10 < LB) ∧ ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C LB) ∧
    (∀ (p : ℕ) [Fact p.Prime], 41 ≤ p → mrCost 3 p (mrRuleH 3 p) < p ∧
      (67 ≤ p → 1 - 399 / 100 * (p : ℝ) ^ (-(1 : ℝ) / 3) ≤ ((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p) ∧
      ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (((p : ℝ) - mrCost 3 p (mrRuleH 3 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 19700000 ≤ p → ∃ C : Gen 3 (ZMod p), QUSep (zcode p) 3 C (1 - 742 / p)) := by
  sorry

end G11

section G12

/-- The conditions of `edValid` at `p = 211` other than the coverings of columns `3` and `4` (kernel-checked), and
`Γ = 209` (`rem:p211`). -/
theorem edP211_valid (h3 : edCover 211 edP211 3 = true) (h4 : edCover 211 edP211 4 = true) :
    edValid 211 edP211 ∧ edCost edP211 = 209 := by
  sorry

/-- **`thm:dim45`, the prime bases** (`tab:dim45`): (a) `s = 4`: `p = 37` (`1/37`) and every prime `p ≥ 47` (`thm:LF`);
(b) `s = 5`: every prime `p ≥ 269` (`thm:LF`); (c) `s = 6`, `s = 7`: every prime `p ≥ 8.607·10^5` resp. `p ≥ 5.322·10^7` (mixed-radix
rule, `thm:MRall`, `tab:P1`), and every prime `p ≥ 281 053` resp. `p ≥ 14 642 759` given `Γ < p` at every prime in
between (hypothesis: the computer-assisted range of `tab:P1`); (d) every `s ≥ 3`: every prime `p > max(p_1(s), s)`,
with `c(P_{sK}) ≥ 1 - C'_s p^{-1/s}` for `p ≥ max(Q_s^s u^{*s}, s)` for any real `u^* > u_min` with `F(u^*) < 1`
(`thm:MRall`), and every prime `p ≥ p_0(s)` with `c(P_{sK}) ≥ 1 - C''_s/p` (`thm:A`). Each: a quasi-uniform digital
`(0,s)`-sequence with the bound on `c(P_{sK})` for every `K ≥ 1`. The Lean statement additionally carries the
conditional conjunct `p = 211`, `s = 5` (`2/211`; hypothesis: the coverings of columns `3`, `4` of the explicit
windows `edP211`), which is `rem:p211` — stronger than the theorem, with the covering hypothesis explicit. -/
theorem dim45_primes :
    (∃ C : Gen 4 (ZMod 37), QUSep (zcode 37) 4 C (1 / 37)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 47 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (67 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (163 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 4 (ZMod p), QUSep (zcode p) 4 C (((p : ℝ) - Γ) / p)) ∧
    (edCover 211 edP211 3 = true → edCover 211 edP211 4 = true →
      edValid 211 edP211 ∧ edCost edP211 = 209 ∧ ∃ C : Gen 5 (ZMod 211), QUSep (zcode 211) 5 C (2 / 211)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 269 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (373 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (1277 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 5 (ZMod p), QUSep (zcode p) 5 C (((p : ℝ) - Γ) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 860700 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
      ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 281053 ≤ p → p < 860700 → mrCost 6 p (mrRuleH 6 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 281053 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
        ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 53220000 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
      ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 14642759 ≤ p → p < 53220000 → mrCost 7 p (mrRuleH 7 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 14642759 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
        ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ (p : ℕ) [Fact p.Prime], mrP1 s < p → s < p → mrCost s p (mrRuleH s p) < p ∧
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ us : ℝ, (mrUmin s : ℝ) < us → mrF s us < 1 →
      ∀ (p : ℕ) [Fact p.Prime], (mrQss s : ℝ) * us ^ s ≤ p → s ≤ p → mrCost s p (mrRuleH s p) < p ∧
        1 - mrCp s us * (p : ℝ) ^ (-(1 : ℝ) / s) ≤ ((p : ℝ) - mrCost s p (mrRuleH s p)) / p ∧
        ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∃ (p0 : ℕ) (C'' : ℝ), ∀ (p : ℕ) [Fact p.Prime], p0 ≤ p →
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (1 - C'' / p)) := by
  sorry

/-- **`thm:dim45` from `thm:S4`**: given the statements `S4_net`, `S4_sep` of `thm:S4`, part (a) `q = 4`
(`c(P_{4K}) ≥ 0.03013`) together with all prime-base parts `dim45_primes`. -/
theorem dim45_of_small (hS4n : IsSeq0 f4code S4gen)
    (hS4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 4 K (seqPoint f4code S4gen) (Real.sqrt 952 / 1024)) :
    QUSep f4code 4 S4gen (3013 / 100000) := by
  sorry

/-- **`thm:dim45`, part (a) `q = 4`** (unconditional; `thm:S4`): a quasi-uniform digital `(0,4)`-sequence over `𝔽_4`
(the sequence `S4gen` of `thm:S4`) with `c(P_{4K}) ≥ 0.03013` for every `K ≥ 1`. With `dim45_primes` this is `thm:dim45`. -/
theorem dim45_q4 : QUSep f4code 4 S4gen (3013 / 100000) := by
  sorry

/-- **`thm:dim45`** (dimensions four and higher; `tab:dim45`): quasi-uniform digital `(0,s)`-sequences with explicit
bounds on `c(P_{sK})` for every `K ≥ 1`: (a) `s = 4`: `q = 4` (the sequence `S4gen` of `thm:S4`, `0.03013`), `p = 37` (`1/37`), every prime
`p ≥ 47`; (b) `s = 5`: every prime `p ≥ 269`; (c) `s = 6, 7`: every prime `p ≥ 8.607·10^5`, `5.322·10^7`, and from
`281 053`, `14 642 759` given `Γ < p` at the primes in between (computer-assisted range); (d) every `s ≥ 3`: every prime
`p > max(p_1(s), s)` (mixed-radix rule, `Γ < p`), with `1 - C'_s p^{-1/s}` for every prime `p ≥ max(Q_s^s u^{*s}, s)`
(any real `u^* > u_min` with `F(u^*) < 1`; `thm:MRall`(c)), and every prime `p ≥ p_0(s)` (staggered rule) with
`1 - C''_s/p` (`dim45_q4`, `dim45_primes`). The Lean statement additionally carries the conditional conjunct
`p = 211`, `s = 5` (`2/211`, given the computer-assisted coverings of columns `3`, `4`), which is `rem:p211` — stronger
than the theorem, with the covering hypothesis explicit. -/
theorem dim45 :
    QUSep f4code 4 S4gen (3013 / 100000) ∧
    (∃ C : Gen 4 (ZMod 37), QUSep (zcode 37) 4 C (1 / 37)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 47 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (67 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (163 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 4 (ZMod p), QUSep (zcode p) 4 C (((p : ℝ) - Γ) / p)) ∧
    (edCover 211 edP211 3 = true → edCover 211 edP211 4 = true →
      edValid 211 edP211 ∧ edCost edP211 = 209 ∧ ∃ C : Gen 5 (ZMod 211), QUSep (zcode 211) 5 C (2 / 211)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 269 ≤ p → ∃ Γ : ℕ, Γ < p ∧ (373 ≤ p → (1 / 10 : ℝ) < ((p : ℝ) - Γ) / p) ∧
      (1277 ≤ p → (3 / 10 : ℝ) ≤ ((p : ℝ) - Γ) / p) ∧ ∃ C : Gen 5 (ZMod p), QUSep (zcode p) 5 C (((p : ℝ) - Γ) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 860700 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
      ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 281053 ≤ p → p < 860700 → mrCost 6 p (mrRuleH 6 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 281053 ≤ p → mrCost 6 p (mrRuleH 6 p) < p ∧
        ∃ C : Gen 6 (ZMod p), QUSep (zcode p) 6 C (((p : ℝ) - mrCost 6 p (mrRuleH 6 p)) / p)) ∧
    (∀ (p : ℕ) [Fact p.Prime], 53220000 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
      ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    ((∀ p : ℕ, p.Prime → 14642759 ≤ p → p < 53220000 → mrCost 7 p (mrRuleH 7 p) < p) →
      ∀ (p : ℕ) [Fact p.Prime], 14642759 ≤ p → mrCost 7 p (mrRuleH 7 p) < p ∧
        ∃ C : Gen 7 (ZMod p), QUSep (zcode p) 7 C (((p : ℝ) - mrCost 7 p (mrRuleH 7 p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ (p : ℕ) [Fact p.Prime], mrP1 s < p → s < p → mrCost s p (mrRuleH s p) < p ∧
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∀ us : ℝ, (mrUmin s : ℝ) < us → mrF s us < 1 →
      ∀ (p : ℕ) [Fact p.Prime], (mrQss s : ℝ) * us ^ s ≤ p → s ≤ p → mrCost s p (mrRuleH s p) < p ∧
        1 - mrCp s us * (p : ℝ) ^ (-(1 : ℝ) / s) ≤ ((p : ℝ) - mrCost s p (mrRuleH s p)) / p ∧
        ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (((p : ℝ) - mrCost s p (mrRuleH s p)) / p)) ∧
    (∀ s : ℕ, 3 ≤ s → ∃ (p0 : ℕ) (C'' : ℝ), ∀ (p : ℕ) [Fact p.Prime], p0 ≤ p →
      ∃ C : Gen s (ZMod p), QUSep (zcode p) s C (1 - C'' / p)) := by
  sorry

end G12

end GeoSeq
