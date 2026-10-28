/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Defs

@[expose] public section

/-!
# Statements: stage V98 (paper V4)

Counting exact digit relations (`sec:count`): `def:exactrel`, `lem:reltype` (polynomial of a relation, degree bound, injectivity, converse, dimension), `thm:count` (refined and depth form), `cor:layer` (a) range form, (b), (c), `cor:N1` (relation form, by the count), `cor:density` (range form), `prop:onerel` ((i) dimension for every scramble; (i) polynomial, (ii), (iii) for self-similar scrambles in residue form), `prop:blockrel` (for every scramble), `lem:rigid`, `cor:residuerows`, `cor:nodesign`.
PROVED (`GeoSeq/V98Cor.lean`, `GeoSeq/V98Count.lean`, `GeoSeq/V98Dim.lean`, `GeoSeq/V98Rel.lean`, `GeoSeq/V98Rigid.lean`, `GeoSeq/V98SS.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V98`
(definitions in `GeoSeq/V98Defs.lean`). Paper: V4 (`paper/sections/07-count.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV98.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F]

/-- If `Res_a(V H / ((z-a)^{K+1} U) dz) = 0` for every polynomial `V`, then `(z - a)^{K+1} ∣ H`. -/
theorem dvd_of_locRes (a : F) (K : ℕ) (H U : F[X]) (hU : U.eval a ≠ 0)
    (h : ∀ V : F[X], locRes a (K + 1) (V * H) U = 0) : (X - C a) ^ (K + 1) ∣ H := by
  sorry

/-- **Uniqueness of the `w`-adic expansion**: if `∑_{j<n} A_j w^j = 0` with `deg A_j < deg w`, all `A_j = 0`. -/
theorem wadic_unique (w : F[X]) (hw : w ≠ 0) :
    ∀ (n : ℕ) (A : ℕ → F[X]), (∀ j < n, (A j).degree < w.degree) →
      ∑ j ∈ range n, A j * w ^ j = 0 → ∀ j < n, A j = 0 := by
  sorry

end G0

section G1
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- `frDigit` is digit `n` of coordinate `c` of the generator matrices `scrGen a L`, read at the index digits
`f_0, …, f_{m-1}` (`lem:resform`(a)). -/
theorem frDigit_vecPoly (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (n : ℕ) (f : ℕ → F) (m : ℕ) :
    frDigit a L c n (vecPoly f m) = ∑ j ∈ range m, scrGen a L c n j * f j := by
  sorry

/-- Per coordinate: `∑_{n ≤ T} f_{c,n} y_{c,n}(V) = ∑_{k ≤ T} g_{c,k} [(z - a_c)^k] V`. -/
theorem place_eq (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) (V : F[X]) :
    ∑ n ∈ range (T + 1), f c n * frDigit a L c n V =
      ∑ k ∈ range (T + 1), relG L f c T k * (taylor (a c) V).coeff k := by
  sorry

/-- **The place-`c` part is a residue** (`lem:reltype`, proof): `∑_{k ≤ T} g_{c,k} [(z-a_c)^k] V =
Res_{a_c}(V A w^{-T-1} dz)` for every polynomial `V`. -/
theorem place_eq_locRes (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) (V : F[X]) :
    ∑ k ∈ range (T + 1), relG L f c T k * (taylor (a c) V).coeff k =
      locRes (a c) (T + 1) (V * relPoly a L f T) (wCo a c ^ (T + 1)) := by
  sorry

/-- The relation form as a sum of residues of `V A / w^{T+1}`. -/
theorem relForm_eq_res (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T : ℕ) (V : F[X]) :
    relForm a L T f V = ∑ c, resAt a (fun _ => T + 1) (V * relPoly a L f T) c := by
  sorry

/-- **`lem:reltype`, degree bound**: for a relation of top index `T` on `P_m`, `deg A < s(T+1) - m`. -/
theorem relPoly_degree_lt (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T m : ℕ) (hf : f ∈ relSpace a L T m) :
    (relPoly a L f T).degree < ((s * (T + 1) - m : ℕ) : WithBot ℕ) := by
  sorry

/-- **`lem:reltype`, injectivity**: the polynomial of a family of top index `T` vanishes only for the zero family. -/
theorem relPoly_eq_zero_iff (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (hL : IsScramble L) (f : Fin s → ℕ → F) (T : ℕ) (hf : ∀ c n, T < n → f c n = 0) :
    relPoly a L f T = 0 ↔ f = 0 := by
  sorry

/-- **`lem:reltype`, the leading digits**: `A(a_c) = f_{c,T} L_c[T][T] w_c(a_c)^{T+1}`; so `f_{c,T} ≠ 0` exactly when
`A(a_c) ≠ 0` (`relPoly_eval_ne_iff`). -/
theorem relPoly_eval (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) :
    (relPoly a L f T).eval (a c) = f c T * L c T T * (wCo a c).eval (a c) ^ (T + 1) := by
  sorry

theorem relPoly_eval_ne_iff (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (hL : IsScramble L) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) :
    (relPoly a L f T).eval (a c) ≠ 0 ↔ f c T ≠ 0 := by
  sorry

/-- **`lem:reltype`, converse**: a family of top index `T` whose polynomial has `deg A < s(T+1) - m` is a relation
on `P_m`. -/
theorem relSpace_of_degree (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T m : ℕ) (hf : ∀ c n, T < n → f c n = 0)
    (hdeg : (relPoly a L f T).degree < ((s * (T + 1) - m : ℕ) : WithBot ℕ)) :
    f ∈ relSpace a L T m := by
  sorry

/-- `lem:reltype`: the polynomial is linear in the relation. -/
theorem relPoly_add (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f g : Fin s → ℕ → F) (T : ℕ) :
    relPoly a L (f + g) T = relPoly a L f T + relPoly a L g T := by
  sorry

theorem relPoly_smul (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (r : F) (f : Fin s → ℕ → F) (T : ℕ) :
    relPoly a L (r • f) T = C r * relPoly a L f T := by
  sorry

end G1

section G2
open Finset Polynomial Module
variable {F : Type*} [Field F] {s : ℕ}

/-- **`lem:reltype`, converse**: every polynomial `B` of degree `< s(T+1)` is the polynomial of exactly one family of
top index `T`. -/
theorem reltype_poly_surj (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (T : ℕ) (B : F[X]) (hB : B.degree < ((s * (T + 1) : ℕ) : WithBot ℕ)) :
    ∃! f : Fin s → ℕ → F, (∀ c n, T < n → f c n = 0) ∧ relPoly a L f T = B := by
  sorry

/-- **`lem:reltype`** (dimension): the relations of top index `T` on `P_m` (with `0`) form a space
of dimension `s(T+1) - m` (truncated subtraction: `0` for `m ≥ s(T+1)`). -/
theorem reltype_dim (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (T m : ℕ) : finrank F (relSpace a L T m) = s * (T + 1) - m := by
  sorry

end G2

section G3
open Finset Polynomial Module
variable {F : Type*} [Field F] {s : ℕ}

/-- **The key step of `thm:count`.** If `g_i` is a relation of top index `K₀ + i` on `P_{s(K₀+i)}` (`i ≤ R`) and
the coordinate-`c` coefficients of the `g_i` add up to zero, then every `g_i` is zero. -/
theorem count_key (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R : ℕ) (hadm : (s - 1) * R + s - 2 < K₀) (g : ℕ → Fin s → ℕ → F)
    (hg : ∀ i ≤ R, g i ∈ relSpace a L (K₀ + i) (s * (K₀ + i)))
    (hsum : ∀ n, ∑ i ∈ range (R + 1), g i c n = 0) : ∀ i ≤ R, g i = 0 := by
  sorry

/-- **`thm:count`, refined form.** Let `[K₀, K₀ + R]` be admissible (`(s-1)R + s - 2 < K₀`), fix a coordinate `c`, and
for every level `T = K₀ + i` let `W_T` be a space of exact digit relations of top index `T` on `P_{sT}` (the
coefficients may depend on `T`) whose coordinate-`c` coefficients vanish outside the digit positions `𝒩`. Then
`∑_T dim W_T ≤ |𝒩|`. -/
theorem count_refined (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R : ℕ) (hadm : (s - 1) * R + s - 2 < K₀) (W : ℕ → Submodule F (Fin s → ℕ → F))
    (hW : ∀ i ≤ R, W (K₀ + i) ≤ relSpace a L (K₀ + i) (s * (K₀ + i))) (𝒩 : Finset ℕ)
    (hN : ∀ i ≤ R, W (K₀ + i) ≤ colSupp c 𝒩) :
    ∑ i ∈ range (R + 1), finrank F (W (K₀ + i)) ≤ 𝒩.card := by
  sorry

/-- **`thm:count`** (counting exact digit relations). Let `[K₀, K₀ + R]` be admissible for depth `J`
(`J ≤ K₀` and `(s-1)R + s - 2 < K₀`) and fix a coordinate `c`. For every level `T = K₀ + i` let `W_T` be a space
of exact digit relations of top index `T` on `P_{sT}` whose depth at coordinate `c` is at most `J` (the depth at the
other coordinates is arbitrary, the coefficients may depend on `T`). Then `∑_{T=K₀}^{K₀+R} dim W_T ≤ J + R + 1`. -/
theorem count (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀)
    (W : ℕ → Submodule F (Fin s → ℕ → F))
    (hW : ∀ i ≤ R, W (K₀ + i) ≤ relSpace a L (K₀ + i) (s * (K₀ + i)))
    (hdepth : ∀ i ≤ R, ∀ f ∈ W (K₀ + i), DepthAt (K₀ + i) J c f) :
    ∑ i ∈ range (R + 1), finrank F (W (K₀ + i)) ≤ J + R + 1 := by
  sorry

end G3

section G4
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **`lem:rigid`** (an exact skeleton relation fixes the row): if `∑_c v_c y_{c,n}(V) = 0` for every `V` with
`deg V ≤ s(n+1) - 2`, `v ≠ 0`, then every `v_c ≠ 0` and `y_{c,n} = (ξ/v_c) ŷ_{c,n}` for one `ξ ≠ 0`. -/
theorem rigid (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L) (n : ℕ)
    (v : Fin s → F) (hv : v ≠ 0) (hrel : skelVec n v ∈ relSpace a L n (s * (n + 1) - 1)) :
    (∀ c, v c ≠ 0) ∧ ∃ ξ : F, ξ ≠ 0 ∧ ∀ c V, frDigit a L c n V = ξ / v c * resDig a c n V := by
  sorry

/-- **`cor:residuerows`, converse direction** (one level): if row `n` is the residue row up to nonzero scalars,
`y_{c,n} = μ_c ŷ_{c,n}`, then `∑_c μ_c^{-1} y_{c,n} = 0` on `P_{s(n+1)-1}` (`lem:resform`(c)). -/
theorem rows_skel (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (n : ℕ) (μ : Fin s → F)
    (hμ : ∀ c, μ c ≠ 0) (hrow : ∀ c V, frDigit a L c n V = μ c * resDig a c n V) :
    skelVec n (fun c => (μ c)⁻¹) ∈ relSpace a L n (s * (n + 1) - 1) := by
  sorry

/-- **`cor:residuerows`** (first part, at one level `n`, `s ≥ 1`): `P_{s(n+1)-1}` satisfies a skeleton relation
`∑_c u_c y_{c,n} = 0` with some `u ≠ 0` iff there are `μ_c ≠ 0` with `y_{c,n} = μ_c ŷ_{c,n}` for all `c`. -/
theorem residuerows (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (n : ℕ) :
    (∃ u : Fin s → F, u ≠ 0 ∧ skelVec n u ∈ relSpace a L n (s * (n + 1) - 1)) ↔
      ∃ μ : Fin s → F, (∀ c, μ c ≠ 0) ∧ ∀ c V, frDigit a L c n V = μ c * resDig a c n V := by
  sorry

/-- `cor:residuerows`: then the check vector of the skeleton relation is proportional to `(1/μ_c)_c`. -/
theorem residuerows_prop (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (n : ℕ) (u μ : Fin s → F) (hu : u ≠ 0) (hrel : skelVec n u ∈ relSpace a L n (s * (n + 1) - 1))
    (hrow : ∀ c V, frDigit a L c n V = μ c * resDig a c n V) :
    ∃ r : F, r ≠ 0 ∧ ∀ c, u c = r * (μ c)⁻¹ := by
  sorry

/-- **`cor:nodesign`** (no designed relation next to skeleton relations). Let `K ≥ max(s-1, sJ)` and suppose the
skeleton relations `∑_c u_{c,n} y_{c,n} = 0` on `P_{s(n+1)-1}` hold at the `J+1` levels `n = K-J, …, K`. Then every
exact digit relation of top index `K` and depth at most `J` on `P_{sK}` is a multiple of `∑_c u_{c,K} y_{c,K} = 0`. -/
theorem nodesign (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (K J : ℕ) (hK1 : s - 1 ≤ K) (hKJ : s * J ≤ K) (u : ℕ → Fin s → F)
    (hu : ∀ n, K - J ≤ n → n ≤ K → u n ≠ 0 ∧ skelVec n (u n) ∈ relSpace a L n (s * (n + 1) - 1))
    (f : Fin s → ℕ → F) (hf : f ∈ relSpace a L K (s * K)) (hdep : ∀ c, DepthAt K J c f) :
    ∃ ν : F, f = ν • skelVec K (u K) := by
  sorry

/-- `cor:nodesign`, "in particular": the full level `P_{sK}` has no designed geometric digit of depth at most `J`
(`s ≥ 2`). -/
theorem nodesign_no_design (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (K J : ℕ) (hK1 : s - 1 ≤ K) (hKJ : s * J ≤ K) (u : ℕ → Fin s → F)
    (hu : ∀ n, K - J ≤ n → n ≤ K → u n ≠ 0 ∧ skelVec n (u n) ∈ relSpace a L n (s * (n + 1) - 1))
    (i : Fin s) (f : Fin s → ℕ → F) : ¬ IsDesign a L J K i f := by
  sorry

end G4

section G5
open Finset Polynomial Module
variable {F : Type*} [Field F] {s : ℕ}

/-- `thm:count` with lower bounds `d_T ≤ dim W_T`, summed over the levels `T ∈ [K₀, K₀ + R]`. -/
theorem count_ge (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀)
    (W : ℕ → Submodule F (Fin s → ℕ → F))
    (hW : ∀ T, K₀ ≤ T → T ≤ K₀ + R → W T ≤ relSpace a L T (s * T) ⊓ depthSub T J c)
    (d : ℕ → ℕ) (hd : ∀ T, K₀ ≤ T → T ≤ K₀ + R → d T ≤ finrank F (W T)) :
    ∑ T ∈ Finset.Icc K₀ (K₀ + R), d T ≤ J + R + 1 := by
  sorry

/-- **`cor:layer`(a)**, range form: if `E` is the set of levels at which all `s` geometric digits of `P_{sT}` are
designed by exact relations of depth at most `J`, then `s · |E ∩ [K₀, K₀+R]| ≤ J + R + 1` for every admissible
range. -/
theorem layer_a (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀) [DecidablePred (AllDesigned a L J)] :
    s * ((Finset.Icc K₀ (K₀ + R)).filter (AllDesigned a L J)).card ≤ J + R + 1 := by
  sorry

/-- **`cor:layer`(b)**: two geometric digits of coordinates `i ≠ i'` are not both designed with depth at most `J`
at all the levels `K₀, …, K₀ + J`, if `K₀ > (s-1)J + s - 2` (`s ≥ 2`). -/
theorem layer_b (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (K₀ J : ℕ) (hadm : (s - 1) * J + s - 2 < K₀) (i i' : Fin s) (hii : i ≠ i')
    (f f' : ℕ → Fin s → ℕ → F)
    (hf : ∀ T, K₀ ≤ T → T ≤ K₀ + J → IsDesign a L J T i (f T) ∧ IsDesign a L J T i' (f' T)) : False := by
  sorry

/-- **`cor:layer`(c)**: a staggered relation `y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` and a skeleton
relation `∑_c u_c y_{c,T} = 0` on `P_{s(T+1)-1}` (any coefficients, `u ≠ 0`) do not both hold at two consecutive
levels `T = K₀, K₀ + 1` with `K₀ ≥ 2s - 2` (`s ≥ 2`). -/
theorem layer_c (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (K₀ : ℕ) (hK : 2 * s - 2 ≤ K₀) (cs : Fin s) (k : ℕ → Fin s → F) (u : ℕ → Fin s → F)
    (hrel : ∀ T, K₀ ≤ T → T ≤ K₀ + 1 → stagVec cs (k T) T ∈ relSpace a L T (s * T) ∧ u T ≠ 0 ∧
      skelVec T (u T) ∈ relSpace a L T (s * (T + 1) - 1)) : False := by
  sorry

/-- **`cor:N1`** (no lattice offset map), relation form, by the refined count at coordinate `1` (V4 route). For
`s = 2`, any two distinct places (e.g. `a = (0, 1)`) over any field, any scramble and `K ≥ 2`, the following three
relations do not hold together: `y_{0,K} = X y_{1,K-1} + (cell digits of coordinate 0)` on `P_{2K}` (`f₁`),
`y_{0,K+1} = X' y_{1,K} + (cell digits of coordinate 0)` on `P_{2K+2}` (`f₂`), and
`y_{1,K} = O y_{1,K-1} + (cell digits of coordinate 0)` on `P_{2K}` (`f₃`): the coefficients of coordinate `1` vanish
outside the indicated positions. (The direct proof of the V3 `prop:N1` is `GeoSeq.N1`.) -/
theorem N1_count (a : Fin 2 → F) (ha : Function.Injective a) (L : Fin 2 → ℕ → ℕ → F) (hL : IsScramble L)
    (K : ℕ) (hK : 2 ≤ K) (f₁ f₂ f₃ : Fin 2 → ℕ → F)
    (h₁ : f₁ ∈ relSpace a L K (2 * K) ∧ f₁ 0 K = 1 ∧ ∀ n, n ≠ K - 1 → f₁ 1 n = 0)
    (h₂ : f₂ ∈ relSpace a L (K + 1) (2 * (K + 1)) ∧ f₂ 0 (K + 1) = 1 ∧ ∀ n, n ≠ K → f₂ 1 n = 0)
    (h₃ : f₃ ∈ relSpace a L K (2 * K) ∧ f₃ 0 K = 0 ∧ f₃ 1 K = 1 ∧ ∀ n, n ≠ K - 1 → n ≠ K → f₃ 1 n = 0) :
    False := by
  sorry

/-- **`cor:density`**, range form. Let `E` be the set of levels `T` at which all `s` geometric digits of `P_{sT}` are
designed by exact relations of depth at most `J`, and `S` the set of levels at which `P_{s(T+1)-1}` satisfies a
skeleton relation. Then `|S ∩ I| + (s-1) |E ∩ I| ≤ J + R + 1` for every admissible range `I = [K₀, K₀ + R]`. -/
theorem density (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀) [DecidablePred (AllDesigned a L J)]
    [DecidablePred (HasSkel a L)] :
    ((Finset.Icc K₀ (K₀ + R)).filter (HasSkel a L)).card +
      (s - 1) * ((Finset.Icc K₀ (K₀ + R)).filter (AllDesigned a L J)).card ≤ J + R + 1 := by
  sorry

/-- **`prop:onerel`(i), dimension part** — here for EVERY scramble of the frame: the level-independent relations
`∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i} = 0` on `P_{sT}` for all `T ≥ T₀` (`T₀ ≥ J`) form a space of dimension at most
one. -/
theorem onerel_dim (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (J T₀ : ℕ) (hJ : J ≤ T₀) : finrank F (liSpace a L J T₀) ≤ 1 := by
  sorry

/-- **`prop:blockrel`** — here for EVERY scramble of the frame: if `d_j` is the dimension of the space of
level-independent relations of class `j` (coefficients the same at all levels `T ≥ T₀` with `T ≡ j (mod ℓ)`, on
`P_{sT}`; `T₀ ≥ J`), then `d_0 + … + d_{ℓ-1} ≤ ℓ`. -/
theorem blockrel (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (ℓ J T₀ : ℕ) (hℓ : 1 ≤ ℓ) (hJ : J ≤ T₀) :
    ∑ j ∈ range ℓ, finrank F (classSpace a L ℓ j J T₀) ≤ ℓ := by
  sorry

end G5

section G6
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
local notation "tw" a:max c:max => ((taylor (a c) (wCo a c) : F[X]) : PowerSeries F)

/-- The residue reading of a self-similar scramble: `y_{c,n}(V) = θ^{n+1} [t^n] V(a_c+t) φ_c w_c(a_c+t)^{-n-1}`. -/
theorem ssL_digit (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (c : Fin s) (n : ℕ) (V : F[X]) :
    frDigit a (ssL a θ φ) c n V =
      θ ^ (n + 1) * PowerSeries.coeff n (((taylor (a c) V : F[X]) : PowerSeries F) *
        (φ c * ((tw a c)⁻¹) ^ (n + 1))) := by
  sorry

/-- A self-similar scramble in residue form is a scramble of the frame (`θ ≠ 0`, unit local multipliers). -/
theorem ssL_scramble (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (φ : Fin s → PowerSeries F)
    (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) : IsScramble (ssL a θ φ) := by
  sorry

/-- **`prop:onerel`(i) (polynomial part) and (ii).** Let a self-similar scramble (residue form, `θ ≠ 0`, unit local
multipliers) satisfy the level-independent relation `∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i} = 0` on the prefixes
`P_{sT+i}` for every `T ≥ T₀ ≥ J` (`i = 0`: on the full levels). Then there is a polynomial `A ≠ 0` with
`deg A < s - i` and `φ_c · ϑ_c(w/θ) = A` as power series at every place `a_c`. -/
theorem onerel_poly (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) (J T₀ i : ℕ) (hJ : J ≤ T₀)
    (ϑ : Fin s → ℕ → F) (hsupp : ∀ c i, J < i → ϑ c i = 0) (hϑ0 : ϑ ≠ 0)
    (hrel : ∀ T, T₀ ≤ T → liEmbed J T ϑ ∈ relSpace a (ssL a θ φ) T (s * T + i)) :
    ∃ A : F[X], A ≠ 0 ∧ A.degree < ((s - i : ℕ) : WithBot ℕ) ∧
      ∀ c, φ c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F) = ((taylor (a c) A : F[X]) : PowerSeries F) := by
  sorry

/-- Constant local multipliers give the residue sequence: `ssL a θ (C ∘ β) = resL a θ β⁻¹`. -/
theorem ssL_const (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (β : Fin s → F)
    (hφ : ∀ c, φ c = PowerSeries.C (β c)) : ssL a θ φ = resL a θ (fun c => (β c)⁻¹) := by
  sorry

/-- **`prop:onerel`(iii), skeleton part.** If a self-similar scramble (residue form) satisfies a skeleton relation
`∑_c v_c y_{c,T} = 0` on `P_{s(T+1)-1}` for every `T ≥ T₀`, `v ≠ 0`, then every `v_c ≠ 0`, `φ_c = α/v_c` for one
`α ≠ 0`, and the scramble is the residue sequence with scale `θ` and check vector `v/α ∝ v` (`ssL = resL`). -/
theorem onerel_skel (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) (T₀ : ℕ) (v : Fin s → F)
    (hv : v ≠ 0) (hrel : ∀ T, T₀ ≤ T → skelVec T v ∈ relSpace a (ssL a θ φ) T (s * (T + 1) - 1)) :
    ∃ α : F, α ≠ 0 ∧ (∀ c, v c ≠ 0 ∧ φ c = PowerSeries.C (α / v c)) ∧
      ssL a θ φ = resL a θ (fun c => v c / α) := by
  sorry

/-- **`cor:residuerows`, self-similar clause.** If a self-similar scramble (residue form) has residue rows up to
scalars, `y_{c,n} = μ_{c,n} ŷ_{c,n}`, at every level `n ≥ n₀`, then its local multipliers are constants and it is the
residue sequence `𝓡_v` with `v_c = φ_c(0)^{-1}`. -/
theorem residuerows_ss (a : Fin s → F) (θ : F) (hθ : θ ≠ 0) (ha : Function.Injective a)
    (φ : Fin s → PowerSeries F) (n₀ : ℕ)
    (hrow : ∀ n, n₀ ≤ n → ∃ μ : Fin s → F, ∀ c V, frDigit a (ssL a θ φ) c n V = μ c * resDig a c n V) :
    ssL a θ φ = resL a θ (fun c => (PowerSeries.constantCoeff (φ c))⁻¹) := by
  sorry

/-- **`prop:onerel`(iii), staggered part.** If a self-similar scramble (residue form) satisfies
`y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` for every `T ≥ T₀ ≥ 1` (`s ≥ 2`), then every `k_c ≠ 0` and, for one
`λ ≠ 0`, `φ_{c⋆} = λ w_{c⋆}` and `φ_c (z - a_{c⋆}) = -λθ/k_c` (`c ≠ c⋆`) as power series: the local multipliers of the
staggered residue sequence with `μ⋆ = λθ`, `μ_c = -μ⋆/k_c` (`onerel_stag_gen`). -/
theorem onerel_stag (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) (hs : 2 ≤ s) (T₀ : ℕ)
    (hT₀ : 1 ≤ T₀) (cs : Fin s) (k : Fin s → F)
    (hrel : ∀ T, T₀ ≤ T → stagVec cs k T ∈ relSpace a (ssL a θ φ) T (s * T)) :
    (∀ c, c ≠ cs → k c ≠ 0) ∧ ∃ lam : F, lam ≠ 0 ∧ φ cs = PowerSeries.C lam * tw a cs ∧
      ∀ c, c ≠ cs → φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) =
        PowerSeries.C (-(lam * θ) / k c) := by
  sorry

/-- `prop:onerel`(iii): the local multipliers found in `onerel_stag` are those of the staggered residue sequence: the
scramble is `𝓡^⋆` with `μ⋆ = λθ` and weights `k` (`ssL = resStarL`, `def:residuestar`). -/
theorem onerel_stag_gen (a : Fin s → F) (ha : Function.Injective a) (θ : F) (φ : Fin s → PowerSeries F)
    (cs : Fin s) (k : Fin s → F) (lam : F) (hcs : φ cs = PowerSeries.C lam * tw a cs)
    (hc : ∀ c, c ≠ cs → φ c * ((taylor (a c) (X - C (a cs)) : F[X]) : PowerSeries F) =
      PowerSeries.C (-(lam * θ) / k c)) :
    ssL a θ φ = resStarL a θ cs (lam * θ) k := by
  sorry

/-- **`prop:onerel`(iii), last sentence** — for every scramble of the frame (in particular every self-similar one):
the staggered relation `y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` and a skeleton relation `∑_c v_c y_{c,T} = 0`
on `P_{s(T+1)-1}` do not both hold at all levels `T ≥ T₀` (`s ≥ 2`; via `cor:layer`(c)). -/
theorem onerel_no_both (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (T₀ : ℕ) (cs : Fin s) (k v : Fin s → F) (hv : v ≠ 0)
    (hstag : ∀ T, T₀ ≤ T → stagVec cs k T ∈ relSpace a L T (s * T))
    (hskel : ∀ T, T₀ ≤ T → skelVec T v ∈ relSpace a L T (s * (T + 1) - 1)) : False := by
  sorry

end G6

end GeoSeq
