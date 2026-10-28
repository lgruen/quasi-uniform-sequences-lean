/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SeriesDefs

@[expose] public section

/-!
# Statements: computable truncated power series and definition fidelity, GeoSeq stage S1

* The bridge `TRep` from lists to `PowerSeries`: sums, scalar multiples, products, inverses, the
  square root `√(1 + a x)`, powers, and the generator entries of a self-similar scramble
  (`GeoSeq/Series.lean`). PROVED.
* Fidelity (kernel `decide`): `ex:running` (`ex_running_C0`, `ex_running_C1`, `ex_running_L1`,
  `ex_running_series`) and `tab:B2dir` (`B2dir_table`) (`GeoSeq/Fidelity.lean`). PROVED.
-/

namespace GeoSeq

open Finset PowerSeries

section Bridge

variable {R : Type*} [CommRing R]

theorem tconst_rep (D : ℕ) (c : R) : TRep D (tconst D c) (C c) := by
  sorry

theorem tone_rep (D : ℕ) : TRep D (tconst D (1 : R)) 1 := by
  sorry

theorem tX_rep (D : ℕ) : TRep D (tX D) (X : PowerSeries R) := by
  sorry

theorem tadd_rep {D : ℕ} {a b : List R} {φ ψ : PowerSeries R} (ha : TRep D a φ) (hb : TRep D b ψ) :
    TRep D (tadd D a b) (φ + ψ) := by
  sorry

theorem tsub_rep {D : ℕ} {a b : List R} {φ ψ : PowerSeries R} (ha : TRep D a φ) (hb : TRep D b ψ) :
    TRep D (tsub D a b) (φ - ψ) := by
  sorry

theorem tscale_rep {D : ℕ} (c : R) {a : List R} {φ : PowerSeries R} (ha : TRep D a φ) :
    TRep D (tscale D c a) (C c * φ) := by
  sorry

/-- **Products**: `[x^n](φ ψ) = ∑_{i ≤ n} [x^i]φ [x^{n-i}]ψ`. -/
theorem tmul_rep {D : ℕ} {a b : List R} {φ ψ : PowerSeries R} (ha : TRep D a φ) (hb : TRep D b ψ) :
    TRep D (tmul D a b) (φ * ψ) := by
  sorry

/-- **Inverses** (`PowerSeries.coeff_inv`): given `c · a_0 = 1`, `tinv D c a` represents `φ⁻¹`. -/
theorem tinv_rep {K : Type*} [Field K] {D : ℕ} {a : List K} {φ : PowerSeries K} (ha : TRep D a φ)
    (c : K) (hc : 0 < D → c * lget a 0 = 1) : TRep D (tinv D c a) φ⁻¹ := by
  sorry

/-- **`√(1 + a x)`**: `tsqrtAux a h N` lists the coefficients `sqrtCoeff p a n`, `n < N`, given
`h = 1/2`. -/
theorem tsqrt_spec {p : ℕ} (a h : ZMod p) (hh : h = (2 : ZMod p)⁻¹) :
    ∀ n N, n < N → lget (tsqrtAux a h N) n = sqrtCoeff p a n := by
  sorry

theorem tsqrt_rep {p : ℕ} (a h : ZMod p) (hh : h = (2 : ZMod p)⁻¹) (D : ℕ) :
    TRep D (tsqrtAux a h D) (rhoWF p a) := by
  sorry

theorem tpows_rep {D : ℕ} {z : List R} {ζ : PowerSeries R} (hz : TRep D z ζ) (K k : ℕ) (hk : k < K) :
    TRep D ((tpows D z K).getD k []) (ζ ^ k) := by
  sorry

/-- **Generator entries of a self-similar scramble**: `[x^n] g_c z_c^k = cget (tcols D K g z) k n`. -/
theorem ssGen_entry {s : ℕ} (g zθ : Fin s → PowerSeries R) (c : Fin s) {D K : ℕ} {gL zL : List R}
    (hg : TRep D gL (g c)) (hz : TRep D zL (zθ c)) (n k : ℕ) (hn : n < D) (hk : k < K) :
    ssGen g zθ c n k = cget (tcols D K gL zL) k n := by
  sorry

/-- **Entries of the scramble `L_c` of a self-similar scramble**:
`[x^n] g_c (z_c - a_c)^i = cget (tcols D K g (z - a)) i n`, `a = z_c(0) = lget z 0`. -/
theorem ssScr_entry {s : ℕ} (g zθ : Fin s → PowerSeries R) (c : Fin s) {D K : ℕ} {gL zL : List R}
    (hg : TRep D gL (g c)) (hz : TRep D zL (zθ c)) (hD : 0 < D) (n i : ℕ) (hn : n < D)
    (hi : i < K) :
    ssScr g zθ c n i = cget (tcols D K gL (tsub D zL (tconst D (lget zL 0)))) i n := by
  sorry

end Bridge

/-! ## Definition fidelity -/

/-- **`ex:running`**: the leading `4 × 4` block of `C_0` of `W^-` in base `7`. -/
theorem ex_running_C0 :
    (Matrix.of fun n k : Fin 4 => WFgen 7 (-1) 0 n k) =
      !![1, 0, 0, 0; 6, 2, 0, 0; 5, 2, 4, 0; 0, 1, 5, 1] := by
  sorry

/-- **`ex:running`**: the leading `4 × 4` block of `C_1` of `W^-` in base `7`. -/
theorem ex_running_C1 :
    (Matrix.of fun n k : Fin 4 => WFgen 7 (-1) 1 n k) =
      !![2, 2, 2, 2; 4, 0, 3, 6; 3, 1, 0, 0; 6, 1, 2, 0] := by
  sorry

/-- **`ex:running`**: the places `a_0 = 0`, `a_1 = 1` and the leading `4 × 4` block of the scramble
`L_1` with `C_1 = L_1 P_1` (`ss_eq_scr`; `C_0 = L_0` since `P_0 = I`). -/
theorem ex_running_L1 :
    ssPlace (WFz 7 (-1)) 0 = 0 ∧ ssPlace (WFz 7 (-1)) 1 = 1 ∧
      (Matrix.of fun n i : Fin 4 => ssScr (WFg 7 (-1)) (WFz 7 (-1)) 1 n i) =
        !![2, 0, 0, 0; 4, 3, 0, 0; 3, 5, 1, 0; 6, 2, 6, 5] := by
  sorry

/-- **`sec:WF`** (the series quoted for the running example): `ρ = 1+3x+6x²+3x³+x⁴+0x⁵+⋯`,
`g_0 = 1+6x+5x²+0x³+0x⁴+0x⁵+⋯`, `g_1 = 2+4x+3x²+6x³+0x⁴+0x⁵+⋯` over `𝔽_7`. -/
theorem ex_running_series :
    (∀ n : Fin 6, coeff n (rhoWF 7 (-1)) = ![1, 3, 6, 3, 1, 0] n) ∧
      (∀ n : Fin 6, coeff n (WFg 7 (-1) 0) = ![1, 6, 5, 0, 0, 0] n) ∧
        (∀ n : Fin 6, coeff n (WFg 7 (-1) 1) = ![2, 4, 3, 6, 0, 0] n) := by
  sorry

/-- **`tab:B2dir`**: column `k < 32` of `C_c` of `thm:B2` (`B2gen`), truncated to its first `32`
digits, is the printed word `M_c[k] = ∑_{n<32} C_c[n][k] 2^{31-n}`. -/
theorem B2dir_table (c : Fin 2) (k : ℕ) (hk : k < 32) :
    ∑ n ∈ range 32, (B2gen c n k).val * 2 ^ (31 - n) = (B2dirTab c).getD k 0 := by
  sorry

end GeoSeq
