/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SeqNet

@[expose] public section

/-!
# GeoSeq stage S1: `lem:t0` (frames have `t = 0`)

As in the paper's proof, via geo results (not re-proved):
* the prefix `P_m` has the truncated generator matrices `L_{c,[m]} P_{a_c,[m]}` (`trunc_scrGen`);
* geo `lem:nie` over a field (`Z3NetF.nie_net_field`): net iff every box minor is nonzero;
* the frame of `s` finite places: its box matrix has the kernel of the Hermite matrix of geo
  `lem:hermite` (`Z3NetF.hermite_ne_zero`, the confluent Vandermonde determinant, which is the
  all-finite-places form of geo `lem:Ts`) (`frame_det_ne`);
* the scrambling identity (geo `eq:scr`) in its kernel form: a lower-triangular `L_c` with nonzero
  diagonal kills nothing in the first `d_c` rows (geo `Z3Net.Proofs.lowerTri_kill`, the lemma behind
  geo `thm:t0` for scrambled frames) (`box_det_scr`). Geo's `gauge_LU` is the graph-form version of
  the same identity; the kernel form avoids converting the frame to a graph form.
-/

namespace GeoSeq

open Finset Matrix

/-- Kernel of a box matrix: `B_d v = 0` iff the first `d_c` digits of every coordinate vanish. -/
lemma box_ker_iff {K : Type*} [CommRing K] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) K)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) (v : Fin m → K) :
    Z3NetF.boxMatrix C d *ᵥ v = 0 ↔ ∀ c (i : Fin m), (i : ℕ) < d c → (C c *ᵥ v) i = 0 := by
  constructor
  · intro h c i hi
    have hrow := Z3NetF.Proofs.box_row_pre C d hd c i hi
    have h1 := congrFun h ⟨Z3NetF.Proofs.pre d c + i, Z3NetF.Proofs.pre_add_lt d hd c i hi⟩
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1 ⊢
    rw [hrow] at h1
    exact h1
  · intro h
    funext r
    obtain ⟨c, i, hi, _, hrow⟩ := Z3NetF.Proofs.box_row_get C d hd r
    have h1 := h c ⟨i, lt_of_lt_of_le hi (Z3NetF.Proofs.le_of_sum d hd c)⟩ hi
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1 ⊢
    rw [hrow]
    exact h1

/-- The scrambling identity, kernel form: left multiplication by lower-triangular matrices with
nonzero diagonal keeps every box minor nonzero (over a field). -/
lemma box_det_scr {K : Type*} [Field K] {s m : ℕ} (L F : Fin s → Matrix (Fin m) (Fin m) K)
    (hlow : ∀ c (i j : Fin m), i < j → L c i j = 0) (hdiag : ∀ c i, L c i i ≠ 0)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) (hF : (Z3NetF.boxMatrix F d).det ≠ 0) :
    (Z3NetF.boxMatrix (fun c => L c * F c) d).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hF
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
  rw [box_ker_iff _ d hd] at hv ⊢
  intro c i hi
  refine Z3Net.Proofs.lowerTri_kill (L c) (hlow c) (fun j => isUnit_iff_ne_zero.mpr (hdiag c j))
    (F c *ᵥ v) (d c) (fun r hr => ?_) i hi
  rw [mulVec_mulVec]
  exact hv c r hr

/-- The frame of `s` distinct finite places has every box minor nonzero (geo `lem:hermite` with
`α_∞ = 0`). -/
lemma frame_det_ne {K : Type*} [Field K] {s m : ℕ} (a : Fin s → K) (ha : Function.Injective a)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    (Z3NetF.boxMatrix (fun c => Z3NetF.readAt m (a c)) d).det ≠ 0 := by
  have hH := Z3NetF.hermite_ne_zero a d 0 (by rw [hd, add_zero])
    (fun P Q hPQ _ _ => ha.ne hPQ)
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hH
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
  have hsum : ∑ P : Fin (s + 1), (if h : (P : ℕ) < s then d ⟨P, h⟩ else 0) = m := by
    rw [Fin.sum_univ_castSucc]
    simp [hd]
  unfold Z3NetF.hermiteMat
  rw [box_ker_iff _ _ hsum]
  rw [box_ker_iff _ d hd] at hv
  intro P i hi
  by_cases hP : (P : ℕ) < s
  · simp only [hP, dite_true] at hi ⊢
    exact hv ⟨P, hP⟩ i hi
  · simp only [hP, dite_false] at hi
    omega

/-- The lower-triangular truncation of a scramble. -/
def lowTrunc {R : Type*} [CommRing R] (L : ℕ → ℕ → R) (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j => if (j : ℕ) ≤ i then L i j else 0

/-- The prefix `P_m` of the scrambled frame has the generator matrices `L_{c,[m]} P_{a_c,[m]}`. -/
lemma trunc_scrGen {R : Type*} [CommRing R] {s : ℕ} (a : Fin s → R) (L : Fin s → ℕ → ℕ → R)
    (m : ℕ) : truncGen (scrGen a L) m = fun c => lowTrunc (L c) m * Z3NetF.readAt m (a c) := by
  funext c i j
  show ∑ x ∈ range ((i : ℕ) + 1), L c i x * pas (a c) x j =
    ∑ x : Fin m, lowTrunc (L c) m i x * Z3NetF.readAt m (a c) x j
  have hi := i.isLt
  calc ∑ x ∈ range ((i : ℕ) + 1), L c i x * pas (a c) x j
      = ∑ x ∈ range m, (if x ≤ (i : ℕ) then L c i x else 0) * pas (a c) x j := by
        apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega))
        · intro x hx
          simp only [mem_sdiff, mem_range] at hx
          simp [show ¬ x ≤ (i : ℕ) by omega]
        · intro x hx
          simp only [mem_range] at hx
          simp [show x ≤ (i : ℕ) by omega]
    _ = ∑ x : Fin m, (if (x : ℕ) ≤ (i : ℕ) then L c i x else 0) * pas (a c) x j :=
        (Fin.sum_univ_eq_sum_range (fun x => (if x ≤ (i : ℕ) then L c i x else 0) *
          pas (a c) x j) m).symm
    _ = ∑ x : Fin m, lowTrunc (L c) m i x * Z3NetF.readAt m (a c) x j := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [lowTrunc, Z3NetF.readAt, pas]

/-- **`lem:t0`** (frames have `t = 0`): for distinct places `a_c ∈ 𝔽_q` and lower-triangular
scrambles `L_c` with nonzero diagonal, `C_c = L_c P_{a_c}` is a `(0,s)`-sequence in base `q`. -/
theorem t0 {R : Type*} [Field R] [Fintype R] [DecidableEq R] {q s : ℕ} [NeZero q]
    (D : DigitCode R q) (a : Fin s → R) (ha : Function.Injective a)
    (L : Fin s → ℕ → ℕ → R) (hL : ∀ c n, L c n n ≠ 0) :
    IsSeq0 D (scrGen a L) := by
  rw [isSeq0_iff_trunc]
  intro m
  rw [Z3NetF.nie_net_field, trunc_scrGen]
  intro d hd
  refine box_det_scr _ _ (fun c i j hij => ?_) (fun c i => ?_) d hd (frame_det_ne a ha d hd)
  · simp [lowTrunc, not_le.mpr hij]
  · simpa [lowTrunc] using hL c i

end GeoSeq
