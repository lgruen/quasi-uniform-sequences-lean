/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2Defs
public import GeoSeq.V0
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

/-!
# GeoSeq stage V2: Cauchy structure (`lem:cauchy`) and the local roots of a simple root

* **`cauchy_mul`**, **`cauchy_super`**, **`cauchy_prod`** = `lem:cauchy` (any field, any frame of distinct
  places, any scale `θ`).
* **`exists_localRoot`**: a simple root `a` of a monic `w` lifts to a local root `z(θx)` with
  `w(z(θx)) = θx`, `z(0) = a` (Hensel's lemma for `F[[x]]`, Mathlib `HenselianRing`); **`faure_roots_exist`**:
  the local roots of the Faure frame `∏_{c<s} (z - c)` over `𝔽_p` exist for `s ≤ p` (any scale).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Cauchy

variable {F : Type*} [Field F] {s : ℕ}

lemma place_sub_ne (zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ)) {c c' : Fin s}
    (h : c ≠ c') : ssPlace zθ c - ssPlace zθ c' ≠ 0 :=
  sub_ne_zero.mpr fun e => h (hinj e)

/-- **`lem:cauchy`**, the identity: `κ_{c←c'} κ_{c'←j} = θ τ(c,c',j) κ_{c←j}` for `c < c' < j` (the `λ_c`
cancel; any frame of distinct places, any scale `θ`, constants `λ_c ≠ 0`). -/
theorem cauchy_mul (θ : F) (lamv : Fin s → F) (hlam : ∀ c, lamv c ≠ 0) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (c c' j : Fin s) (h1 : c < c') (h2 : c' < j) :
    kapL θ lamv zθ c c' * kapL θ lamv zθ c' j = θ * tauC zθ c c' j * kapL θ lamv zθ c j := by
  have e1 := place_sub_ne zθ hinj (ne_of_gt h1)
  have e2 := place_sub_ne zθ hinj (ne_of_gt h2)
  have e3 := place_sub_ne zθ hinj (ne_of_gt (h1.trans h2))
  have w1 := placeDer_ne_zero zθ hinj c
  have w2 := placeDer_ne_zero zθ hinj c'
  have l1 := hlam c; have l2 := hlam c'; have l3 := hlam j
  unfold kapL tauC
  field_simp

/-- The constants of `lem:cauchy` with a prescribed superdiagonal: `λ_0 = 1`,
`λ_t = λ_{t-1} θ / (d_t w'(a_{t-1}) (a_t - a_{t-1}))` (indices `≥ s` are not used). -/
noncomputable def cauchyLam (θ : F) (zθ : Fin s → PowerSeries F) (d : Fin s → F) : ℕ → F
  | 0 => 1
  | t + 1 => cauchyLam θ zθ d t * θ /
      ((if h : t + 1 < s then d ⟨t + 1, h⟩ else 1) *
        (if h : t < s then placeDer zθ ⟨t, h⟩ else 1) *
        ((if h : t + 1 < s then ssPlace zθ ⟨t + 1, h⟩ else 0) -
          (if h : t < s then ssPlace zθ ⟨t, h⟩ else 0)))

lemma cauchyLam_ne (θ : F) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (d : Fin s → F) (hd : ∀ t, d t ≠ 0) :
    ∀ t, t < s → cauchyLam θ zθ d t ≠ 0 := by
  intro t
  induction t with
  | zero => intro _; simp [cauchyLam]
  | succ t ih =>
    intro ht
    simp only [cauchyLam, dif_pos ht, dif_pos (show t < s by omega)]
    have := ih (by omega)
    have h1 := hd ⟨t + 1, ht⟩
    have h2 := placeDer_ne_zero zθ hinj ⟨t, by omega⟩
    have h3 := place_sub_ne zθ hinj (c := ⟨t + 1, ht⟩) (c' := ⟨t, by omega⟩)
      (by rw [Ne, Fin.ext_iff]; simp)
    exact div_ne_zero (mul_ne_zero this hθ) (mul_ne_zero (mul_ne_zero h1 h2) h3)

/-- **`lem:cauchy`**, the free superdiagonal: for any `d_1, …, d_{s-1} ≠ 0` there are constants
`λ_c ≠ 0` with `κ_{t-1←t} = d_t` (`t ≥ 1`; `d_0` is not used). -/
theorem cauchy_super (θ : F) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (d : Fin s → F) (hd : ∀ t, d t ≠ 0) :
    ∃ lamv : Fin s → F, (∀ c, lamv c ≠ 0) ∧
      ∀ t : Fin s, 1 ≤ t.val → kapL θ lamv zθ (predF t) t = d t := by
  refine ⟨fun c => cauchyLam θ zθ d c.val,
    fun c => cauchyLam_ne θ hθ zθ hinj d hd c.val c.isLt, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, t.val = u + 1 := ⟨t.val - 1, by omega⟩
  have hus : u < s := by omega
  have hpt : predF t = ⟨u, hus⟩ := Fin.ext (by simp [predF, hu])
  have ht' : t = ⟨u + 1, by omega⟩ := Fin.ext hu
  rw [hpt]
  have hl := cauchyLam_ne θ hθ zθ hinj d hd u hus
  have h2 := placeDer_ne_zero zθ hinj ⟨u, hus⟩
  have h3 := place_sub_ne zθ hinj (c := t) (c' := ⟨u, hus⟩) (by rw [Ne, Fin.ext_iff]; simp [hu])
  have h1 := hd t
  unfold kapL
  simp only [hu, cauchyLam, dif_pos (show u + 1 < s by omega), dif_pos hus]
  rw [← ht']
  field_simp

/-- **`lem:cauchy`**, the product formula: if `κ_{t-1←t} = d_t` for all `t ≥ 1`, then for `c < j`
`κ_{c←j} = d_{c+1} ⋯ d_j / ∏_{i=c+2}^{j} θ τ(c, i-1, i)`. -/
theorem cauchy_prod (θ : F) (hθ : θ ≠ 0) (lamv : Fin s → F) (hlam : ∀ c, lamv c ≠ 0)
    (zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ)) (d : Fin s → F)
    (hsup : ∀ t : Fin s, 1 ≤ t.val → kapL θ lamv zθ (predF t) t = d t) (c j : Fin s) (hcj : c < j) :
    kapL θ lamv zθ c j =
      (∏ i ∈ univ.filter (fun i : Fin s => c < i ∧ i ≤ j), d i) /
        ∏ i ∈ univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j), θ * tauC zθ c (predF i) i := by
  classical
  suffices H : ∀ k (j : Fin s), j.val = c.val + 1 + k → kapL θ lamv zθ c j =
      (∏ i ∈ univ.filter (fun i : Fin s => c < i ∧ i ≤ j), d i) /
        ∏ i ∈ univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j), θ * tauC zθ c (predF i) i by
    exact H (j.val - c.val - 1) j (by rw [Fin.lt_def] at hcj; omega)
  intro k
  induction k with
  | zero =>
    intro j hj
    have hp : predF j = c := Fin.ext (by simp [predF]; omega)
    have hs1 : univ.filter (fun i : Fin s => c < i ∧ i ≤ j) = {j} := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.lt_def, Fin.le_def,
        Fin.ext_iff]; omega
    have hs2 : univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j) = ∅ := by
      ext i; simp only [mem_filter, mem_univ, true_and, Fin.le_def, notMem_empty, iff_false]; omega
    rw [hs1, hs2, prod_singleton, prod_empty, div_one, ← hsup j (by omega), hp]
  | succ k ih =>
    intro j hj
    set j' := predF j
    have hj' : j'.val = c.val + 1 + k := by simp [j', predF]; omega
    have h1 : c < j' := by rw [Fin.lt_def]; omega
    have h2 : j' < j := by rw [Fin.lt_def]; omega
    have hm := cauchy_mul θ lamv hlam zθ hinj c j' j h1 h2
    rw [hsup j (by omega)] at hm
    have hs1 : univ.filter (fun i : Fin s => c < i ∧ i ≤ j) =
        insert j (univ.filter (fun i : Fin s => c < i ∧ i ≤ j')) := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def, Fin.le_def,
        Fin.ext_iff]; omega
    have hs2 : univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j) =
        insert j (univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j')) := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.le_def, Fin.ext_iff]; omega
    have hn1 : j ∉ univ.filter (fun i : Fin s => c < i ∧ i ≤ j') := by
      simp only [mem_filter, mem_univ, true_and, Fin.le_def, not_and, not_le]; intro; omega
    have hn2 : j ∉ univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j') := by
      simp only [mem_filter, mem_univ, true_and, Fin.le_def, not_and, not_le]; intro; omega
    rw [hs1, hs2, prod_insert hn1, prod_insert hn2]
    have ihj := ih j' hj'
    have e1 := place_sub_ne zθ hinj (ne_of_gt h1)
    have e2 := place_sub_ne zθ hinj (ne_of_gt h2)
    have e3 := place_sub_ne zθ hinj (ne_of_gt (h1.trans h2))
    have w2 := placeDer_ne_zero zθ hinj j'
    have hτ : θ * tauC zθ c j' j ≠ 0 := by
      unfold tauC
      exact mul_ne_zero hθ (div_ne_zero e3 (mul_ne_zero (mul_ne_zero w2 e1) e2))
    have hq : ∏ i ∈ univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j'),
        θ * tauC zθ c (predF i) i ≠ 0 := by
      rw [prod_ne_zero_iff]
      intro i hi
      simp only [mem_filter, mem_univ, true_and, Fin.le_def] at hi
      have hc1 : c < predF i := by rw [Fin.lt_def]; simp [predF]; omega
      have hc2 : predF i < i := by rw [Fin.lt_def]; simp [predF]; omega
      unfold tauC
      exact mul_ne_zero hθ (div_ne_zero (place_sub_ne zθ hinj (ne_of_gt (hc1.trans hc2)))
        (mul_ne_zero (mul_ne_zero (placeDer_ne_zero zθ hinj _) (place_sub_ne zθ hinj (ne_of_gt hc1)))
          (place_sub_ne zθ hinj (ne_of_gt hc2))))
    have hτ' : tauC zθ c j' j ≠ 0 := right_ne_zero_of_mul hτ
    have : kapL θ lamv zθ c j = kapL θ lamv zθ c j' * d j / (θ * tauC zθ c j' j) := by
      rw [hm]; field_simp
    rw [this, ihj, show predF j = j' from rfl]
    field_simp

end Cauchy

section Roots

/-- **Local roots exist** (Hensel's lemma over `F[[x]]`): a simple root `a` of a monic polynomial `w`
(`w(a) = 0`, `w'(a) ≠ 0`) lifts, for every scale `θ`, to a power series `z = z(θx)` with
`w(z(θx)) = θx` and `z(0) = a`. -/
theorem exists_localRoot {F : Type*} [Field F] (w : F[X]) (hw : w.Monic) (a : F)
    (ha : w.eval a = 0) (hd : w.derivative.eval a ≠ 0) (θ : F) :
    ∃ z : PowerSeries F, Polynomial.aeval z w = C θ * X ∧ constantCoeff z = a := by
  have hdeg : 0 < w.natDegree := by
    by_contra h
    have h0 : w.natDegree = 0 := by omega
    rw [Polynomial.Monic.natDegree_eq_zero hw] at h0
    rw [h0] at ha; simp at ha
  set f : (PowerSeries F)[X] := w.map C - Polynomial.C (C θ * X) with hf_def
  have hmap : (w.map (C : F →+* PowerSeries F)).Monic := hw.map _
  have hfm : f.Monic := by
    refine hmap.sub_of_left ?_
    refine (Polynomial.degree_C_le).trans_lt ?_
    rw [Polynomial.Monic.degree_map hw (C : F →+* PowerSeries F)]
    rw [Polynomial.degree_eq_natDegree hw.ne_zero]
    exact_mod_cast hdeg
  have heval : ∀ y : PowerSeries F, f.eval y = Polynomial.aeval y w - C θ * X := by
    intro y
    rw [hf_def, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map, Polynomial.aeval_def]
    rfl
  have h1 : f.eval (C a) ∈ Ideal.span {(X : PowerSeries F)} := by
    rw [heval, Polynomial.aeval_def]
    have : Polynomial.eval₂ (algebraMap F (PowerSeries F)) (C a) w = C (w.eval a) := by
      rw [show (C a : PowerSeries F) = algebraMap F (PowerSeries F) a from rfl,
        Polynomial.eval₂_at_apply]; rfl
    rw [this, ha, map_zero, zero_sub]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  have h2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(X : PowerSeries F)})
      (f.derivative.eval (C a))) := by
    have e : f.derivative.eval (C a) = C (w.derivative.eval a) := by
      rw [hf_def, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
        Polynomial.derivative_map, Polynomial.eval_map,
        show (C a : PowerSeries F) = (C : F →+* PowerSeries F) a from rfl, Polynomial.eval₂_at_apply]
    rw [e]
    exact ((isUnit_iff_ne_zero.mpr hd).map C).map _
  obtain ⟨z, hz, hz'⟩ := HenselianRing.is_henselian f hfm (C a) h1 h2
  refine ⟨z, ?_, ?_⟩
  · have := hz.eq_zero
    rw [heval] at this
    exact sub_eq_zero.mp this
  · rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, constantCoeff_C] at hz'
    exact sub_eq_zero.mp hz'

lemma natCast_inj_lt (p : ℕ) {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-- The Faure frame `∏_{c<s} (z - c)` is monic of degree `s`. -/
theorem faureW_monic (s p : ℕ) : (faureW s p).Monic := Polynomial.monic_prod_X_sub_C _ _

theorem faureW_natDegree (s p : ℕ) [Fact p.Prime] : (faureW s p).natDegree = s := by
  unfold faureW
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, sum_const, card_range, smul_eq_mul, mul_one]

/-- **The local roots of the Faure frame exist** (`s ≤ p`, any scale `θ`): power series
`z_c(θx)`, `c < s`, with `∏_b (z_c(θx) - b) = θx` and `z_c(0) = c`. -/
theorem faure_roots_exist (s p : ℕ) [Fact p.Prime] (hsp : s ≤ p) (θ : ZMod p) :
    ∃ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (faureW s p) = C θ * X) ∧
      ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p) := by
  have h : ∀ c : Fin s, ∃ z : PowerSeries (ZMod p),
      Polynomial.aeval z (faureW s p) = C θ * X ∧ constantCoeff z = ((c : ℕ) : ZMod p) := by
    intro c
    have hc : (c : ℕ) ∈ range s := mem_range.mpr c.isLt
    have hfac : faureW s p = (Polynomial.X - Polynomial.C ((c : ℕ) : ZMod p)) *
        ∏ b ∈ (range s).erase c, (Polynomial.X - Polynomial.C (b : ZMod p)) :=
      (Finset.mul_prod_erase _ (fun b : ℕ => Polynomial.X - Polynomial.C (b : ZMod p)) hc).symm
    refine exists_localRoot _ (faureW_monic s p) _ ?_ ?_ θ
    · rw [hfac]; simp
    · rw [hfac, Polynomial.derivative_mul]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]
      rw [Polynomial.eval_prod, prod_ne_zero_iff]
      intro b hb
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      intro he
      have := natCast_inj_lt p (lt_of_lt_of_le c.isLt hsp)
        (lt_of_lt_of_le (mem_range.mp (mem_of_mem_erase hb)) hsp) he
      exact (ne_of_mem_erase hb) this.symm
  choose zθ hz using h
  exact ⟨zθ, fun c => (hz c).1, fun c => (hz c).2⟩

end Roots

end GeoSeq
