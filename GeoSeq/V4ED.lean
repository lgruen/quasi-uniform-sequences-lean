/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4Core

@[expose] public section

/-!
# GeoSeq stage V4: explicit ordered windows with exact coverings (`thm:LF`(b))

* `enumAll_sound`, `winTest_sound`: the enumeration of `𝔽_p^j` and the window test are sound.
* `ed_kap`: the crosses are the stored integers (`θ λ_c ≡ κ_{c←j} λ_j w'(a_c)(a_j - a_c)`).
* **`ed_sound`**: for explicit ordered windows valid at `p` (`edValid`), selection rules exist and every
  selection rule gives a quasi-uniform digital `(0,s)`-sequence with `c(P_{sK}) ≥ (p - Γ)/p` for every `K`.
* `ed_seq`: existential form.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {s : ℕ}

lemma enumAll_sound (p : ℕ) (test : List ℕ → Bool) : ∀ (k : ℕ) (σ0 : List ℕ), enumAll p test k σ0 = true →
    ∀ τ : List ℕ, τ.length = k → (∀ x ∈ τ, x < p) → test (σ0 ++ τ) = true := by
  intro k
  induction k with
  | zero =>
    intro σ0 h τ hτ _
    rw [List.length_eq_zero_iff.mp hτ, List.append_nil]; exact h
  | succ k ih =>
    intro σ0 h τ hτ hlt
    cases τ with
    | nil => simp at hτ
    | cons x τ' =>
      simp only [enumAll] at h
      have hx := List.all_eq_true.mp h x (List.mem_range.mpr (hlt x List.mem_cons_self))
      have := ih (σ0 ++ [x]) hx τ' (by simpa using hτ) (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
      rwa [List.append_assoc, List.singleton_append] at this

/-- The natural-number window test is sound: `(σ + ((y + B) mod p)) mod p ≤ 2B` gives
`σ + y ∈ [-B, B]` modulo `p`. -/
lemma natTest_sound (p : ℕ) [NeZero p] (σ : ZMod p) (y : ℤ) (B : ℕ)
    (h : (σ.val + ((y + B) % (p : ℤ)).toNat) % p ≤ 2 * B) :
    σ + (y : ZMod p) ∈ intWin p (-(B : ℤ)) B := by
  set r := (σ.val + ((y + B) % (p : ℤ)).toNat) % p with hr
  have h1 : ((((y + B) % (p : ℤ)).toNat : ℕ) : ZMod p) = ((y + B : ℤ) : ZMod p) := by
    have : ((((y + B) % (p : ℤ)).toNat : ℕ) : ℤ) = (y + B) % (p : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne p))
    rw [← Int.cast_natCast, this, ZMod.intCast_mod]
  refine ⟨(r : ℤ) - B, by omega, by omega, ?_⟩
  calc (((r : ℤ) - B : ℤ) : ZMod p) = (r : ZMod p) - B := by push_cast; ring
    _ = ((σ.val + ((y + B) % (p : ℤ)).toNat : ℕ) : ZMod p) - B := by rw [hr, ZMod.natCast_mod]
    _ = σ + y := by push_cast [h1, ZMod.natCast_zmod_val]; ring

/-- The sum `B_c = ∑_{j > c} B_{c←j}` of `def:lex` over `Fin s` is the sum over `j ∈ (c, s)`. -/
lemma lexB_eq_sum (f : ℕ → ℕ → ℕ) (c : Fin s) :
    lexB (fun c j : Fin s => f c j) c = ∑ j ∈ Ioo (c : ℕ) s, f c j := by
  classical
  unfold lexB
  rw [Finset.sum_filter]
  have e : ∀ c' : Fin s, (if c < c' then f c c' else 0) =
      (fun j : ℕ => if (c : ℕ) < j then f c j else 0) c' := fun c' => by
    simp only [Fin.lt_def]
  rw [Finset.sum_congr rfl (fun c' _ => e c'),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if (c : ℕ) < j then f c j else 0) s, ← Finset.sum_filter]
  congr 1; ext j; simp only [mem_filter, mem_range, mem_Ioo]; omega

section Main

variable {p : ℕ} [Fact p.Prime]

/-- **The crosses of explicit ordered windows** are the stored integers. -/
theorem ed_kap (E : EDesign s) (hv : edValid p E) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA E.frame c : ℤ) : ZMod p)) (c j : Fin s) (hcj : c < j) :
    kapL (edTheta E p) (edLam E p) zθ c j = (edK E c j : ZMod p) := by
  obtain ⟨hd, -, hl, hk, -⟩ := hv
  have hcj' : (c : ℕ) < j := hcj
  have h := (hk j j.isLt c hcj').1
  have hc : (((E.th * edLamZ E c - edK E c j * edLamZ E j * frameW s E.frame c *
      (frameA E.frame j - frameA E.frame c) : ℤ)) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero h)
  push_cast at hc
  unfold kapL edTheta edLam
  rw [frame_placeDer s E.frame zθ hplace c]
  simp only [ssPlace, hplace]
  have hne : (edLamZ E j : ZMod p) * ((frameW s E.frame c : ℤ) : ZMod p) *
      (((frameA E.frame j : ℤ) : ZMod p) - ((frameA E.frame c : ℤ) : ZMod p)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (intCast_ne_zero_of_emod (hl j j.isLt)) (frameW_ne s E.frame hd c.isLt))
      (sub_ne_zero.mpr (frame_ne s E.frame hd j.isLt c.isLt (by omega)))
  rw [div_eq_iff hne]
  linear_combination hc

/-- **Explicit ordered windows** (`thm:LF`(b)): if `edValid p E` (`s ≥ 1`, `p ≥ 5`), then for every choice of
the local roots selection rules exist, and every selection rule defines a quasi-uniform digital
`(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`, `Γ = edCost E`. -/
theorem ed_sound (E : EDesign s) (hs : 1 ≤ s) (hp : 5 ≤ p) (hv : edValid p E)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s E.frame) = C (edTheta E p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA E.frame c : ℤ) : ZMod p)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (edTheta E p) (edLam E p) zθ (edWin E p) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (edTheta E p) (edLam E p) zθ (edWin E p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ))
        (((p : ℝ) - edCost E) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - edCost E) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (edTheta E p) (edLam E p) zθ rule) zθ)))) := by
  have hv' := hv
  obtain ⟨hd, hth, hl, hk, hlex, hcost, hcov⟩ := hv'
  have hlex' : IsLexData p (fun c : Fin s => edA E c) (fun c => edM E c) (fun c j => edBx E c j) := by
    intro c
    rw [lexB_eq_sum (fun c j => edBx E c j) c]
    exact hlex c c.isLt
  refine lex_sound p hp hs E.frame hd (edTheta E p) (intCast_ne_zero_of_emod hth) (edLam E p)
    (fun c => intCast_ne_zero_of_emod (hl c c.isLt)) zθ hroot hplace _ _ _ hlex' hcost
    (fun c j => edK E c j) (fun c j hcj => ed_kap E hv zθ hplace c j hcj)
    (fun c j hcj => (hk j j.isLt c hcj).2) (fun j σ => ?_)
  -- the covering of column `j` from the enumeration
  have hM : 1 ≤ edM E j := (hlex j j.isLt).1
  by_cases hj0 : (j : ℕ) = 0
  · exact ⟨-(edA E j : ℤ), by omega, le_rfl, fun c hc => absurd hc (by rw [Fin.lt_def]; omega)⟩
  have hjs := j.isLt
  set pre : List ℕ := (List.range ((j : ℕ) - 1)).map
    (fun c => if h : c < s then (σ ⟨c, h⟩).val else 0) with hpre
  have hc0 := hcov j j.isLt
  unfold edCover at hc0
  rw [if_neg hj0] at hc0
  have ht := enumAll_sound p _ ((j : ℕ) - 1) [] hc0 pre (by simp [hpre])
    (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      split_ifs
      · exact ZMod.val_lt _
      · exact Nat.pos_of_ne_zero (NeZero.ne p))
  rw [List.nil_append] at ht
  set jl : Fin s := ⟨(j : ℕ) - 1, by omega⟩ with hjl
  have hx := List.all_eq_true.mp ht (σ jl).val (List.mem_range.mpr (ZMod.val_lt _))
  obtain ⟨rs, hrs, hxr⟩ := List.any_eq_true.mp hx
  rw [List.mem_filter] at hrs
  obtain ⟨hrs1, hrs2⟩ := hrs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrs1
  rw [List.mem_range] at hi
  refine ⟨-((edA E j : ℤ) + edM E j - 1) + i, by omega, by omega, fun c hc => ?_⟩
  have hc' : (c : ℕ) < j := hc
  have hrsc : ((List.range (j : ℕ)).map fun c => edOff p E j c i).getD c 0 = edOff p E j c i := by
    rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  have key : ((σ c).val + edOff p E j c i) % p ≤ 2 * edBx E c j := by
    rcases (show (c : ℕ) < (j : ℕ) - 1 ∨ (c : ℕ) = (j : ℕ) - 1 by omega) with hlt | heq
    · have h := List.all_eq_true.mp hrs2 c (List.mem_range.mpr hlt)
      rw [decide_eq_true_eq, hrsc] at h
      have hpc : pre.getD c 0 = (σ c).val := by
        rw [hpre, List.getD_eq_getElem _ _ (by simp; omega)]; simp [c.isLt]
      have hBc : ((List.range (j : ℕ)).map fun c => edBx E c j).getD c 0 = edBx E c j := by
        rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
      rwa [hpc, hBc] at h
    · rw [decide_eq_true_eq] at hxr
      have hcj : c = jl := Fin.ext heq
      rw [← heq, hrsc] at hxr
      rw [hcj]; rw [hcj] at hxr
      exact hxr
  have := natTest_sound p (σ c) ((-((edA E j : ℤ) + edM E j - 1) + i) * edK E c j) (edBx E c j) key
  push_cast at this ⊢
  exact this

/-- **Explicit ordered windows give a sequence** (existential form of `ed_sound`). -/
theorem ed_seq (E : EDesign s) (hs : 1 ≤ s) (hp : 5 ≤ p) (hv : edValid p E) :
    ∃ C : Gen s (ZMod p), IsSeq0 (zcode p) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) C) (((p : ℝ) - edCost E) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
          Real.sqrt s * p / (((p : ℝ) - edCost E) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  obtain ⟨zθ, hroot, hplace⟩ := frame_roots_exist p s E.frame hv.1 (edTheta E p)
  obtain ⟨⟨rule, hrule⟩, hall⟩ := ed_sound E hs hp hv zθ hroot hplace
  exact ⟨_, hall rule hrule⟩

end Main

end GeoSeq
