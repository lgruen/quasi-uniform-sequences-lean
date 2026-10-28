/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S11Defs

@[expose] public section

/-!
# Statements: geoseq stage S11 (Appendix C machinery, `app:machinery`)

The residue theorem of the Faure frame and `lem:residue` (`s = 2`), the local roots and the curvature
series `γ`, the e-basis (`T_c`, `B_c`), `lem:ebasis`, the change of coordinate `w ↔ t` and the e-basis form
of `prop:LI`(a) (Faure frame), `prop:LIconv`, the level-invariant clause of `prop:N2`(a), and
`rem:convchar2` for all levels. Compared theorems (statement with `sorry`; proofs in `GeoSeq/S11Res.lean`,
`S11Series.lean`, `EBasis.lean`, `LIa.lean`, `LIconv.lean`, `ConvChar2.lean`, restated by name; generated
from the proof files' signatures by script, with the section variables of each proof file).

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-! ## From `GeoSeq/S11Res.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The residue theorem of the Faure frame** (`lem:residue`, `s = 2`; the residue theorem on `ℙ¹` for
`V dz / (z^A (z-1)^B)`, holomorphic at `∞` when `deg V ≤ A + B - 2`): `Res_0 + Res_1 = 0`, where
`Res_0 = [z^{A-1}] V(z) (z-1)^{-B}` and `Res_1 = [t^{B-1}] V(1+t) (1+t)^{-A}`. -/
theorem residue2 (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (V : F[X]) (hV : V.natDegree + 2 ≤ A + B) :
    coeff (A - 1) ((Polynomial.taylor (0 : F) V : PS) * ((X + C (-1)) ^ B)⁻¹) +
      coeff (B - 1) ((Polynomial.taylor (1 : F) V : PS) * ((X + C 1) ^ A)⁻¹) = 0 := by
  sorry

/-! ## From `GeoSeq/S11Series.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** `T + T² = w`. -/
theorem tRoot_add_sq : (tRoot : PS) + tRoot ^ 2 = X := by
  sorry

theorem gamF_zero : coeff 0 (gamF : PS) = 1 := by
  sorry

theorem gamF_one : coeff 1 (gamF : PS) = 2 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** In characteristic two `γ = 1 + T²` has only even coefficients. -/
theorem gamF_odd (h2 : (2 : F) = 0) (n : ℕ) (hn : n % 2 = 1) : coeff n (gamF : PS) = 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** `γ(t (t + δ)) = (t + δ)²` for `δ² = 1`. -/
theorem gamF_subst_wD (δ : F) (hδ : δ * δ = 1) : (gamF : PS).subst (wD δ) = (X + C δ) ^ 2 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **Change of coordinate** `w ↔ t` (the residue is invariant): `[w^j] f = [t^j] f(t(t + δ)) ·
(2t + δ) (t + δ)^{-(j+1)}`, `δ² = 1`. Here `(2t + δ) dt = dw` and `w^{-j-1} = t^{-j-1} (t + δ)^{-j-1}`. -/
theorem coeff_change (δ : F) (hδ : δ * δ = 1) (f : PS) (j : ℕ) :
    coeff j f = coeff j (f.subst (wD δ) * ((C 2 * X + C δ) * ((X + C δ) ^ (j + 1))⁻¹)) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The curvature identity**: `[t^K] P (t + δ)^{-K} = ∑_{n ≤ K} γ_n [t^{K-n}] P (t + δ)^{-(K-n+2)}`
(`δ² = 1`): the polar part of `w^{-K} dz/(z - a_{1-c})` at `a_c` in the e-basis, from
`(t + δ)² = γ(t(t + δ))`. -/
theorem gam_expand (δ : F) (hδ : δ * δ = 1) (P : PS) (K : ℕ) :
    coeff K (P * ((X + C δ) ^ K)⁻¹) =
      ∑ n ∈ range (K + 1), coeff n gamF * coeff (K - n) (P * ((X + C δ) ^ (K - n + 2))⁻¹) := by
  sorry

/-! ## From `GeoSeq/EBasis.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The matrices `B_c`** (`app:machinery`): `ε_{c,i} = ∑_{j ≤ i} B_c[i][j] y_{c,j}`. -/
theorem ebas_B_exists (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) :
    ∃ B : Fin 2 → ℕ → ℕ → F, ∀ c i V,
      ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The matrices `T_c`** (`app:machinery`): `η_{c,n} ≡ ∑_{k ≤ n} T_c[n][k] e_{c,k}`, i.e.
`y_{c,n} = ∑_{k ≤ n} T_c[n][k] ε_{c,k}`. -/
theorem ebas_T_exists (L : Fin 2 → ℕ → ℕ → F) :
    ∃ T : Fin 2 → ℕ → ℕ → F, ∀ c n V,
      scrDig (faurePl c) (L c) n V = ∑ k ∈ range (n + 1), T c n k * ebas c k V := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** The e-basis functionals are linearly independent: `T_c` is unique. -/
theorem ebas_indep (c : Fin 2) (n : ℕ) (d : ℕ → F)
    (hd : ∀ V, ∑ k ∈ range (n + 1), d k * ebas c k V = 0) : ∀ k ≤ n, d k = 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** `B_c[i][i] ≠ 0` (the diagonal of `B_c` is the inverse of the diagonal of `T_c`). -/
theorem B_diag_ne (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (c : Fin 2) (i : ℕ) : B c i i ≠ 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The residue theorem for `Φ_K^{(c)}`** (`lem:residue`): `Res_{a_0}(VΦ) + Res_{a_1}(VΦ) = 0` for
`deg V < 2K`, `K ≥ 1`. -/
theorem residue_thm (K : ℕ) (hK : 1 ≤ K) (c : Fin 2) (V : F[X]) (hV : V.natDegree < 2 * K) :
    resPhi K c 0 V + resPhi K c 1 V = 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:residue`** (`s = 2`, Faure frame): if `η_{c,K} ≡ λ Φ_K^{(c)} + ∑_{j<K} o_j η_{c,j}` at `a_c` and
`Φ_K^{(c)} ≡ ∑_{j<K} ξ_j η_{c',j}` at `a_{c'}` (`c' ≠ c`; as functionals: equal residues against every
polynomial), then for every `V` with `deg V < 2K`:
`r_c = y_{c,K} = ∑_{j<K} o_j y_{c,j} - λ ∑_{j<K} ξ_j y_{c',j}`. -/
theorem residue_faure (L : Fin 2 → ℕ → ℕ → F) (K : ℕ) (hK : 1 ≤ K) (c c' : Fin 2) (hcc : c' ≠ c)
    (lam : F) (o ξ : ℕ → F)
    (hown : ∀ V, scrDig (faurePl c) (L c) K V =
      lam * resPhi K c c V + ∑ j ∈ range K, o j * scrDig (faurePl c) (L c) j V)
    (hoth : ∀ V, resPhi K c c' V = ∑ j ∈ range K, ξ j * scrDig (faurePl c') (L c') j V)
    (V : F[X]) (hV : V.natDegree < 2 * K) :
    scrDig (faurePl c) (L c) K V = ∑ j ∈ range K, o j * scrDig (faurePl c) (L c) j V -
      lam * ∑ j ∈ range K, ξ j * scrDig (faurePl c') (L c') j V := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** The decompositions of `lem:residue` exist, with `λ ≠ 0` (`K ≥ 1`, nonzero diagonal). -/
theorem residue_decomp (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (c c' : Fin 2) (hcc : c' ≠ c) :
    (∃ lam : F, lam ≠ 0 ∧ ∃ o : ℕ → F, ∀ V, scrDig (faurePl c) (L c) K V =
        lam * resPhi K c c V + ∑ j ∈ range K, o j * scrDig (faurePl c) (L c) j V) ∧
      ∃ ξ : ℕ → F, ∀ V, resPhi K c c' V = ∑ j ∈ range K, ξ j * scrDig (faurePl c') (L c') j V := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:ebasis`** (law of an arbitrary scramble of the Faure frame in the e-basis, both coordinates):
let `B_c` express the e-basis in the rows (`ε_{c,i} = ∑_{j ≤ i} B_c[i][j] y_{c,j}`; they exist by
`ebas_B_exists`). At every level `K ≥ 1`, for every `V` with `deg V < 2K`,
`r_c = y_{c,K} = ∑_{j<K} (-F^{(c)}_j / F^{(c)}_K) y_{c,j} + ∑_{j<K} (-T_c[K][K] B_{c'}[K-1][j]) y_{c',j}`
with `F^{(c)}_j = ∑_{n ≤ K-j} γ_n B_c[K-n][j]`, `F^{(c)}_K = B_c[K][K]` and `T_c[K][K] = 1/B_c[K][K]`:
(i) the cross coefficient of `y_{c',j}` in `r_c` is `-T_c[K][K] B_{c'}[K-1][j]`; (ii) the own coefficient is
`-F_j/F_K`. -/
theorem ebasis (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (K : ℕ) (hK : 1 ≤ K) (V : F[X]) (hV : V.natDegree < 2 * K) (c c' : Fin 2) (hcc : c' ≠ c) :
    scrDig (faurePl c) (L c) K V =
      ∑ j ∈ range K, (-(∑ n ∈ range (K - j + 1), coeff n (gamF : PS) * B c (K - n) j) / B c K K) *
          scrDig (faurePl c) (L c) j V +
        ∑ j ∈ range K, (-(B c' (K - 1) j) / B c K K) * scrDig (faurePl c') (L c') j V := by
  sorry

/-! ## From `GeoSeq/LIa.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The e-basis in the coordinate `w`** (change of coordinate, `θ = 1`):
`ε_{c,j}(V) = [w^j] u_c(w) V(z_c(w))`. -/
theorem ebas_eq_w (c : Fin 2) (j : ℕ) (V : F[X]) :
    ebas c j V = coeff j (uF c * Polynomial.aeval (zF c) V) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The e-basis in the coordinate `x = w/θ`**: `θ^j ε_{c,j}(V) = [x^j] u_c(θx) V(z_c(θx))`. -/
theorem ebas_eq_x (θ : F) (c : Fin 2) (j : ℕ) (V : F[X]) :
    θ ^ j * ebas c j V =
      coeff j (rescale θ (uF c) * Polynomial.aeval (rescale θ (zF c)) V) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:LI`(a)** (e-basis characterisation, Faure frame): with `T_c` the matrix of the rows in the
e-basis (`y_{c,n} = ∑_{k ≤ n} T_c[n][k] ε_{c,k}`), coordinate `c` is self-similar with scale `θ ≠ 0`
(`y_{c,n}(V) = [x^n] g(x) V(z_c(θx))` with `g(0) ≠ 0`) iff `T_c[n][k] = λ θ^n φ_{n-k}` for `k ≤ n`, with
`λ ≠ 0`, `φ(0) = 1` (`T_c = diag(λ θ^n) · Toep(φ)`). The correspondence is `λ φ(θx) = g(x)/u_c(θx)`. -/
theorem LI_a (L : Fin 2 → ℕ → ℕ → F) (T : Fin 2 → ℕ → ℕ → F)
    (hT : ∀ c n V, scrDig (faurePl c) (L c) n V = ∑ k ∈ range (n + 1), T c n k * ebas c k V)
    (θ : F) (hθ : θ ≠ 0) (c : Fin 2) :
    (∃ g : PS, constantCoeff g ≠ 0 ∧ ∀ n V,
        scrDig (faurePl c) (L c) n V = coeff n (g * Polynomial.aeval (rescale θ (zF c)) V)) ↔
      (∃ lam : F, lam ≠ 0 ∧ ∃ φ : PS, constantCoeff φ = 1 ∧
        ∀ n k, k ≤ n → T c n k = lam * θ ^ n * coeff (n - k) φ) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** `prop:LI`(a) from the inverse matrix: if `B_c[i][j] = μ θ^{-i} χ_{i-j}` (`μ ≠ 0`, `χ(0) ≠ 0`), then
coordinate `c` is self-similar with scale `θ`, multiplier `g = u_c(θx) / (μ χ(x))`. -/
theorem LI_a_B (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (θ : F) (hθ : θ ≠ 0) (c : Fin 2) (μ : F) (hμ : μ ≠ 0) (χ : PS) (hχ : constantCoeff χ ≠ 0)
    (hform : ∀ i j, j ≤ i → B c i j = μ * (θ ^ i)⁻¹ * coeff (i - j) χ) :
    ∃ g : PS, constantCoeff g ≠ 0 ∧ ∀ n V,
      scrDig (faurePl c) (L c) n V = coeff n (g * Polynomial.aeval (rescale θ (zF c)) V) := by
  sorry

/-- **Self-similar scrambles as generator matrices** (`def:selfsim`): the scrambled Faure frame equals
`ssGen g zθ` iff the digit functionals of every coordinate are `V ↦ [x^n] g_c V(zθ_c)`. -/
theorem scrGen_eq_ssGen_iff (L : Fin 2 → ℕ → ℕ → F) (g zθ : Fin 2 → PS) :
    scrGen faurePl L = ssGen g zθ ↔
      ∀ c n V, scrDig (faurePl c) (L c) n V = coeff n (g c * Polynomial.aeval (zθ c) V) := by
  sorry

/-! ## From `GeoSeq/LIconv.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:LIconv`** (the converse in dimension two): let `q` be odd or `q = 2` (`2 ≠ 0` in `F`, or
`|F| = 2`). If the law of a scramble of the Faure frame (`a_0 = 0`, `a_1 = 1`, `L_c` lower triangular
with nonzero diagonal) is level-invariant, then the scramble is self-similar with one common scale
`θ ≠ 0`: `C_c = ssGen g (z_c(θx))` (`def:selfsim`) with multipliers `g_c(0) ≠ 0`. In particular
`X^{(1)}_{0←1} X^{(1)}_{1←0} = θ²` (the depth-0 cross responses at level `1`). -/
theorem LIconv [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0 ∨ Fintype.card F = 2)
    (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (hLI : LevelInv (scrGen faurePl L)) :
    ∃ θ : F, θ ≠ 0 ∧
      (∃ g : Fin 2 → PS, (∀ c, constantCoeff (g c) ≠ 0) ∧
        scrGen faurePl L = ssGen g (fun c => rescale θ (zF c))) ∧
      ∀ d01 d10 : F, IsCarryEntry (scrGen faurePl L) 1 0 1 0 1 d01 →
        IsCarryEntry (scrGen faurePl L) 1 0 1 1 0 d10 → d01 * d10 = θ ^ 2 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:N2`(a), level-invariant clause**: for `q` odd or `q = 2`, if the law of a scramble of the
Faure frame is level-invariant, the own responses `D(l)[1][1]` and the cross responses `D(l)[0][1]`
(at every level) have generating functions that are not both rational. -/
theorem N2a_LI [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0 ∨ Fintype.card F = 2)
    (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (hLI : LevelInv (scrGen faurePl L))
    (o x : ℕ → F)
    (ho : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (scrGen faurePl L) K 0 l 1 1 (o l))
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (scrGen faurePl L) K 0 l 0 1 (x l)) :
    ¬ (IsRatPS (PowerSeries.mk o) ∧ IsRatPS (PowerSeries.mk x)) := by
  sorry

/-! ## From `GeoSeq/ConvChar2.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`rem:convchar2`** (characteristic two, every level): let `2 = 0` in the finite field `F` and
`ω ∉ {0, 1}` (such `ω` exists iff `q = 2^r ≥ 4`). The scramble `convL ω` of the Faure frame has nonzero
diagonal and a level-invariant law (earlier `def:LI`; own responses `-∑_{m ≤ l} γ_m`, cross responses `-1` at
every level `K`), but it is self-similar for no scale `θ` and no multipliers. -/
theorem convchar2 [Fintype F] [DecidableEq F] (h2 : (2 : F) = 0) (ω : F) (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) :
    (∀ c n, convL ω c n n ≠ 0) ∧ LevelInv (scrGen faurePl (convL ω)) ∧
      ∀ θ : F, ∀ g : Fin 2 → PS, scrGen faurePl (convL ω) ≠ ssGen g (fun c => rescale θ (zF c)) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`rem:convchar2`, existence form**: in every finite field of characteristic two with `q ≥ 4`
elements there is a scramble of the Faure frame with a level-invariant law that is self-similar for no
scale. -/
theorem convchar2_exists [Fintype F] [DecidableEq F] (h2 : (2 : F) = 0) (hq : 4 ≤ Fintype.card F) :
    ∃ L : Fin 2 → ℕ → ℕ → F, (∀ c n, L c n n ≠ 0) ∧ LevelInv (scrGen faurePl L) ∧
      ∀ θ : F, ∀ g : Fin 2 → PS, scrGen faurePl L ≠ ssGen g (fun c => rescale θ (zF c)) := by
  sorry

end GeoSeq
