/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Series

@[expose] public section

/-!
# GeoSeq stage S1: definition fidelity by kernel `decide`

The definitions `WFgen` (`def:WF`) and `B2gen` (`thm:B2`) reproduce the printed data of the paper:
the leading `4 × 4` blocks of `C_0`, `C_1` and of the scramble `L_1` of the running example
`ex:running` (`W^-`, `p = 7`), the series `ρ`, `g_0`, `g_1` quoted in `sec:WF`, and the 64 words of
`tab:B2dir`. Each entry is rewritten to a computable truncated-series expression (`GeoSeq/Series.lean`),
which the kernel evaluates (`decide +kernel`: a kernel reduction of the `Decidable` instance; no
`native_decide`, no extra axioms).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## The running example: `W^-` in base `7` -/

/-- `1/2 = 4` in `𝔽_7` (the inverse of `ZMod`, as used by `sqrtCoeff`). -/
lemma half_seven : (4 : ZMod 7) = (2 : ZMod 7)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by decide)

/-- `ρ = √(1 - x)` over `𝔽_7`, `D` coefficients. -/
def rho7 (D : ℕ) : List (ZMod 7) := tsqrtAux (-1) 4 D

def wfg0L (D : ℕ) : List (ZMod 7) :=
  tmul D (tmul D (tconst D 2) (rho7 D))
    (tinv D 4 (tmul D (tsub D (tconst D 1) (tX D)) (tadd D (tconst D 1) (rho7 D))))

def wfg1L (D : ℕ) : List (ZMod 7) := tmul D (tadd D (tconst D 1) (rho7 D)) (tinv D 1 (rho7 D))

def wfz0L (D : ℕ) : List (ZMod 7) := tscale D 4 (tsub D (tconst D 1) (rho7 D))

def wfz1L (D : ℕ) : List (ZMod 7) := tscale D 4 (tadd D (tconst D 1) (rho7 D))

lemma rho7_rep (D : ℕ) : TRep D (rho7 D) (rhoWF 7 (-1)) := tsqrt_rep _ _ half_seven D

lemma wfz_eq (c : Fin 2) : WFz 7 (-1) c =
    ![C 4 * (1 - rhoWF 7 (-1)), C 4 * (1 + rhoWF 7 (-1))] c := by
  have h : (2 : ZMod 7)⁻¹ = 4 := (eq_inv_of_mul_eq_one_left (by decide : (4 : ZMod 7) * 2 = 1)).symm
  unfold WFz
  rw [h]

lemma wfg0_rep : TRep 6 (wfg0L 6) (WFg 7 (-1) 0) :=
  tmul_rep (tmul_rep (tconst_rep 6 2) (rho7_rep 6))
    (tinv_rep (tmul_rep (tsub_rep (tone_rep 6) (tX_rep 6)) (tadd_rep (tone_rep 6) (rho7_rep 6)))
      4 (fun _ => by decide +kernel))

lemma wfg1_rep : TRep 6 (wfg1L 6) (WFg 7 (-1) 1) :=
  tmul_rep (tadd_rep (tone_rep 6) (rho7_rep 6)) (tinv_rep (rho7_rep 6) 1 (fun _ => by decide +kernel))

lemma wfz0_rep (D : ℕ) : TRep D (wfz0L D) (WFz 7 (-1) 0) := by
  rw [wfz_eq]
  exact tscale_rep 4 (tsub_rep (tone_rep D) (rho7_rep D))

lemma wfz1_rep (D : ℕ) : TRep D (wfz1L D) (WFz 7 (-1) 1) := by
  rw [wfz_eq]
  exact tscale_rep 4 (tadd_rep (tone_rep D) (rho7_rep D))

/-- **`ex:running`**: the leading `4 × 4` block of `C_0` of `W^-` in base `7`. -/
theorem ex_running_C0 :
    (Matrix.of fun n k : Fin 4 => WFgen 7 (-1) 0 n k) =
      !![1, 0, 0, 0; 6, 2, 0, 0; 5, 2, 4, 0; 0, 1, 5, 1] := by
  ext n k
  simp only [Matrix.of_apply]
  refine (ssGen_entry (WFg 7 (-1)) (WFz 7 (-1)) 0 (K := 4) wfg0_rep (wfz0_rep 6) n k
    (by have := n.isLt; omega) k.isLt).trans ?_
  revert n k; decide +kernel

/-- **`ex:running`**: the leading `4 × 4` block of `C_1` of `W^-` in base `7`. -/
theorem ex_running_C1 :
    (Matrix.of fun n k : Fin 4 => WFgen 7 (-1) 1 n k) =
      !![2, 2, 2, 2; 4, 0, 3, 6; 3, 1, 0, 0; 6, 1, 2, 0] := by
  ext n k
  simp only [Matrix.of_apply]
  refine (ssGen_entry (WFg 7 (-1)) (WFz 7 (-1)) 1 (K := 4) wfg1_rep (wfz1_rep 6) n k
    (by have := n.isLt; omega) k.isLt).trans ?_
  revert n k; decide +kernel

/-- **`ex:running`**: the places `a_0 = 0`, `a_1 = 1` and the leading `4 × 4` block of the scramble
`L_1` with `C_1 = L_1 P_1` (`ss_eq_scr`; `C_0 = L_0` since `P_0 = I`). -/
theorem ex_running_L1 :
    ssPlace (WFz 7 (-1)) 0 = 0 ∧ ssPlace (WFz 7 (-1)) 1 = 1 ∧
      (Matrix.of fun n i : Fin 4 => ssScr (WFg 7 (-1)) (WFz 7 (-1)) 1 n i) =
        !![2, 0, 0, 0; 4, 3, 0, 0; 3, 5, 1, 0; 6, 2, 6, 5] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ssPlace, ← coeff_zero_eq_constantCoeff_apply, ← wfz0_rep 6 0 (by norm_num)]
    decide +kernel
  · rw [ssPlace, ← coeff_zero_eq_constantCoeff_apply, ← wfz1_rep 6 0 (by norm_num)]
    decide +kernel
  · ext n i
    simp only [Matrix.of_apply]
    refine (ssScr_entry (WFg 7 (-1)) (WFz 7 (-1)) 1 (K := 4) wfg1_rep (wfz1_rep 6) (by norm_num)
      n i (by have := n.isLt; omega) i.isLt).trans ?_
    revert n i; decide +kernel

/-- **`sec:WF`** (the series quoted for the running example): `ρ = 1+3x+6x²+3x³+x⁴+0x⁵+⋯`,
`g_0 = 1+6x+5x²+0x³+0x⁴+0x⁵+⋯`, `g_1 = 2+4x+3x²+6x³+0x⁴+0x⁵+⋯` over `𝔽_7`. -/
theorem ex_running_series :
    (∀ n : Fin 6, coeff n (rhoWF 7 (-1)) = ![1, 3, 6, 3, 1, 0] n) ∧
      (∀ n : Fin 6, coeff n (WFg 7 (-1) 0) = ![1, 6, 5, 0, 0, 0] n) ∧
        (∀ n : Fin 6, coeff n (WFg 7 (-1) 1) = ![2, 4, 3, 6, 0, 0] n) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · rw [← rho7_rep 6 n n.isLt]; revert n; decide +kernel
  · rw [← wfg0_rep n n.isLt]; revert n; decide +kernel
  · rw [← wfg1_rep n n.isLt]; revert n; decide +kernel

/-! ## `tab:B2dir` -/

def uL (D : ℕ) : List (ZMod 2) := (List.range D).map uB2coeff

def b2g0L (D : ℕ) : List (ZMod 2) := tmul D (tadd D (tconst D 1) (tX D)) (tadd D (tconst D 1) (uL D))

def b2g1L (D : ℕ) : List (ZMod 2) := (List.range D).map fun n => uB2coeff (n + 1)

def b2z1L (D : ℕ) : List (ZMod 2) := tadd D (tconst D 1) (uL D)

lemma uL_rep (D : ℕ) : TRep D (uL D) uB2 := fun n hn => by
  rw [uL, lget_map_range _ hn, uB2, coeff_mk]

lemma b2g_rep (D : ℕ) (c : Fin 2) : TRep D (![b2g0L D, b2g1L D] c) (B2g c) := by
  fin_cases c
  · exact tmul_rep (tadd_rep (tone_rep D) (tX_rep D)) (tadd_rep (tone_rep D) (uL_rep D))
  · intro n hn
    show lget (b2g1L D) n = coeff n (mk fun n => uB2coeff (n + 1))
    rw [b2g1L, lget_map_range _ hn, coeff_mk]

lemma b2z_rep (D : ℕ) (c : Fin 2) : TRep D (![uL D, b2z1L D] c) (B2z c) := by
  fin_cases c
  · exact uL_rep D
  · exact tadd_rep (tone_rep D) (uL_rep D)

/-- The 32-bit word of a column (digit `0` in the most significant bit). -/
def b2word (col : List (ZMod 2)) : ℕ := ((List.range 32).map fun n => (lget col n).val * 2 ^ (31 - n)).sum

set_option maxRecDepth 100000 in
/-- The computed columns give the printed words (kernel evaluation of 64 columns of 32 digits). -/
lemma b2_words : ∀ c : Fin 2,
    (tcols 32 32 (![b2g0L 32, b2g1L 32] c) (![uL 32, b2z1L 32] c)).map b2word = B2dirTab c := by
  decide +kernel

lemma word_getD (M : List (List (ZMod 2))) (k : ℕ) (hk : k < M.length) :
    ((List.range 32).map fun n => (cget M k n).val * 2 ^ (31 - n)).sum = (M.map b2word).getD k 0 := by
  have hget : M.getD k [] = M[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
    Option.getD_some]
  unfold cget b2word
  rw [hget]

/-- **`tab:B2dir`**: column `k < 32` of `C_c` of `thm:B2` (`B2gen`), truncated to its first `32`
digits, is the printed word `M_c[k] = ∑_{n<32} C_c[n][k] 2^{31-n}`. -/
theorem B2dir_table (c : Fin 2) (k : ℕ) (hk : k < 32) :
    ∑ n ∈ range 32, (B2gen c n k).val * 2 ^ (31 - n) = (B2dirTab c).getD k 0 := by
  have e : ∀ n ∈ range 32, (B2gen c n k).val * 2 ^ (31 - n) =
      (cget (tcols 32 32 (![b2g0L 32, b2g1L 32] c) (![uL 32, b2z1L 32] c)) k n).val *
        2 ^ (31 - n) := fun n hn => by
    rw [show B2gen c n k = _ from
      ssGen_entry B2g B2z c (b2g_rep 32 c) (b2z_rep 32 c) n k (mem_range.mp hn) hk]
  rw [Finset.sum_congr rfl e, ← lsum_range, word_getD _ k (by rw [tcols_length]; exact hk),
    b2_words c]

end GeoSeq
