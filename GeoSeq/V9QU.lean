/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Kor

@[expose] public section

/-!
# GeoSeq stage V9-2 (part 5): quasi-uniformity in index form, and the explicit residue theorem

The Palomar statement (`HeadlineSeqV4/Challenge_combined_explicit.lean`) writes the toroidal distance with
`round` and the covering radius / minimum distance with minima over indices. This file proves the residue
results in exactly these forms, so that the headline bridge (V9-H) is definitional.

* `torDistR_eq`: on `[0,1]^s`, `|t - round t| = min(|t|, 1 - |t|)` coordinatewise, so `torDistR = torDist2`.
* `covRadIdx_le`: `h(P_{[N]}) ≤ √s q N^{-1/s}` for a `(0,s)`-sequence (from `prefix_cov`);
  `sepDistIdx_ge`: `δ(P_{[N]}) ≥ b N^{-1/s}` from `SepAllN` (Euclidean `≥` toroidal on `[0,1]^s`);
  `qu_of_sepAllN`: a `(0,s)`-sequence with `δ(P_{[N]}) ≥ b N^{-1/s}`, `b > 0`, is quasi-uniform (mesh ratio
  `≤ √s q / b`; this is the "in particular" of `lem:prefix`).
* `residue_qu` (**`cor:residueQU`**, index form): `ℓ_jit(Λ_v) ≥ L > 0` ⇒ `𝓡_v` quasi-uniform.
* `residue_korobov_explicit`: **`thm:residue` + `cor:korobov` + `cor:residueQU`** for the paper's explicit
  sequence in the Palomar statement's form.
-/

namespace GeoSeq

open Finset

variable {s : ℕ}

/-! ## The toroidal distance with `round` -/

lemma sub_round_sq (d : ℝ) (hd : |d| ≤ 1) :
    (d - round d) ^ 2 = (min |d| (1 - |d|)) ^ 2 := by
  rw [round_eq]
  rcases lt_or_ge d (-1 / 2) with h1 | h1
  · have hf : ⌊d + 1 / 2⌋ = -1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [(abs_le.mp hd).1]
    rw [hf, abs_of_neg (by linarith), min_eq_right (by linarith)]
    push_cast; ring
  rcases lt_or_ge d (1 / 2) with h2 | h2
  · have hf : ⌊d + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [hf, min_eq_left (by rcases abs_cases d with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)]
    push_cast; rw [sub_zero, sq_abs]
  · have hf : ⌊d + 1 / 2⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [(abs_le.mp hd).2]
    rw [hf, abs_of_pos (by linarith), min_eq_right (by linarith)]
    push_cast; ring

/-- On `[0,1]^s` the two forms of the toroidal distance agree. -/
theorem torDistR_eq (x y : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hy : ∀ c, 0 ≤ y c ∧ y c ≤ 1) :
    torDistR x y = Z3NetDGS.torDist2 x y := by
  unfold torDistR Z3NetDGS.torDist2 Z3NetDGS.torCoord
  congr 1
  refine Finset.sum_congr rfl fun c _ => sub_round_sq _ ?_
  have := hx c; have := hy c
  rw [abs_le]; constructor <;> linarith

lemma torDist2_le_euclDist (x y : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1)
    (hy : ∀ c, 0 ≤ y c ∧ y c ≤ 1) : Z3NetDGS.torDist2 x y ≤ euclDist x y := by
  unfold Z3NetDGS.torDist2 euclDist Z3NetDGS.torCoord
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
  have := hx c; have := hy c
  have h1 : |x c - y c| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h0 : 0 ≤ min |x c - y c| (1 - |x c - y c|) := le_min (abs_nonneg _) (by linarith)
  rw [← sq_abs (x c - y c)]
  exact pow_le_pow_left₀ h0 (min_le_left _ _) 2

/-! ## Covering radius and minimum distance over indices -/

section Idx
variable {R : Type*} [CommRing R] {q : ℕ} [NeZero q]

lemma seqPoint_mem (hq : 2 ≤ q) (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) :
    0 ≤ seqPoint D C v c ∧ seqPoint D C v c ≤ 1 := by
  have := coord_cell hq D C v c 0
  simp only [pow_zero, one_mul] at this
  have h0 : cellIdx D C v c 0 = 0 := by simp [cellIdx]
  rw [h0] at this
  simpa using this

/-- `h(P_{[N]}) ≤ √s q N^{-1/s}` with the minimum over indices. -/
theorem covRadIdx_le (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (N : ℕ) (hN : 1 ≤ N) :
    covRadIdx (seqPoint D C) N ≤ Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) := by
  have hcov := prefix_cov D C hq hs hseq N hN
  have hne : Nonempty {x : Fin s → ℝ // ∀ c, x c ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩⟩
  unfold covRadIdx
  refine ciSup_le fun x => ?_
  have hx : ∀ c, 0 ≤ x.1 c ∧ x.1 c ≤ 1 := fun c => x.2 c
  set P := prefixSet N (seqPoint D C)
  have hmem : ∀ v, v < N → seqPoint D C v ∈ P := fun v hv =>
    Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, rfl⟩
  have hPne : Nonempty P := ⟨⟨_, hmem 0 (by omega)⟩⟩
  -- the inner minimum over indices is at most the one over the point set
  have h1 : (⨅ v : Fin N, euclDist x.1 (seqPoint D C v)) ≤ ⨅ y : P, euclDist x.1 y.1 := by
    refine le_ciInf fun y => ?_
    obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp y.2
    have hbdd : BddBelow (Set.range fun v : Fin N => euclDist x.1 (seqPoint D C v)) :=
      ⟨0, by rintro _ ⟨v, rfl⟩; exact Real.sqrt_nonneg _⟩
    refine (ciInf_le hbdd ⟨v, Finset.mem_range.mp hv⟩).trans_eq ?_
    rw [← hvy]
  -- the inner minimum over the point set is at most the covering radius
  have h2 : (⨅ y : P, euclDist x.1 y.1) ≤ Z3NetDGS.covRad euclDist P := by
    have hbdd : BddAbove (Set.range fun x : {x : Fin s → ℝ // ∀ j, 0 ≤ x j ∧ x j ≤ 1} =>
        ⨅ y : P, euclDist x.1 y.1) := by
      refine ⟨Real.sqrt s, ?_⟩
      rintro _ ⟨z, rfl⟩
      have hb : BddBelow (Set.range fun y : P => euclDist z.1 y.1) :=
        ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
      refine (ciInf_le hb ⟨_, hmem 0 (by omega)⟩).trans ?_
      unfold euclDist
      refine Real.sqrt_le_sqrt ?_
      calc ∑ c, (z.1 c - seqPoint D C 0 c) ^ 2 ≤ ∑ _c : Fin s, (1 : ℝ) := by
            refine Finset.sum_le_sum fun c _ => ?_
            have := z.2 c; have := seqPoint_mem hq D C 0 c
            nlinarith
        _ = s := by simp
    exact le_ciSup hbdd ⟨x.1, hx⟩
  exact h1.trans (h2.trans hcov)

/-- `δ(P_{[N]}) ≥ b N^{-1/s}` with the minimum over pairs of distinct indices (Euclidean), from the toroidal
`SepAllN`. -/
theorem sepDistIdx_ge (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (b : ℝ)
    (hsep : SepAllN s (seqPoint D C) b) (N : ℕ) (hN : 2 ≤ N) :
    b * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ sepDistIdx (seqPoint D C) N := by
  have hne : Nonempty {vw : Fin N × Fin N // vw.1 ≠ vw.2} :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
  unfold sepDistIdx
  refine le_ciInf fun vw => ?_
  have hvw : (vw.1.1 : ℕ) ≠ vw.1.2 := fun h => vw.2 (Fin.ext h)
  exact (hsep N hN _ _ vw.1.1.isLt vw.1.2.isLt hvw).trans
    (torDist2_le_euclDist _ _ (seqPoint_mem hq D C _) (seqPoint_mem hq D C _))

/-- `lem:prefix`, "in particular": a `(0,s)`-sequence with `δ(P_{[N]}) ≥ b N^{-1/s}` (`b > 0`, every `N ≥ 2`)
is quasi-uniform, with mesh ratio `≤ √s q / b`. -/
theorem qu_of_sepAllN (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (b : ℝ) (hb : 0 < b) (hsep : SepAllN s (seqPoint D C) b) :
    IsQuasiUniform (seqPoint D C) := by
  refine ⟨Real.sqrt s * q / b, fun N hN => ?_⟩
  have h1 := covRadIdx_le D C hq hs hseq N (by omega)
  have h2 := sepDistIdx_ge D C hq b hsep N hN
  have hfac : 0 ≤ Real.sqrt s * q / b := by positivity
  calc covRadIdx (seqPoint D C) N ≤ Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) := h1
    _ = Real.sqrt s * q / b * (b * (N : ℝ) ^ (-(1 / (s : ℝ)))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hfac

end Idx

/-! ## Residue sequences -/

variable {p : ℕ}

/-- **`cor:residueQU`** (index form): if every nonzero `b ∈ Λ_v` has `‖(|b| - 𝟏)_+‖_2 ≥ L > 0`, the residue
sequence is quasi-uniform. -/
theorem residue_qu [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) :
    IsQuasiUniform (seqPoint (zcode p) (resSeq a θ v)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  exact qu_of_sepAllN (zcode p) _ (Fact.out : p.Prime).two_le (by omega)
    (resSeq_t0 (zcode p) a ha θ hθ v hv) _
    (div_pos (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hp) _) hL0) (by exact_mod_cast hp))
    (residue_allN hs a ha θ hθ v hv L hL0.le hL)

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
  have hpr : p.Prime := Fact.out
  obtain ⟨h1, h2, h3, h4, -⟩ := residue_korobov hs hps
  refine ⟨h1, fun K hK v w hv hw hvw => ?_, ?_⟩
  · rw [torDistR_eq _ _ (seqPoint_mem hpr.two_le _ _ v) (seqPoint_mem hpr.two_le _ _ w)]
    exact h2 K hK v w hv hw hvw
  · exact qu_of_sepAllN (zcode p) _ hpr.two_le (by omega) h1 _
      (div_pos h3 (by exact_mod_cast hpr.pos)) h4

end GeoSeq
