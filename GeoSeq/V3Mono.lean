/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V3Defs
public import GeoSeq.V2

@[expose] public section

/-!
# GeoSeq stage V3: monotonicity of `F` and `u F(u)` (second half of `lem:MRbound`)

The closure argument of the paper's proof: a function `f` on `(a, ∞)` (`a ≥ 0`) is in the class `MonoU a` if it
is nonnegative and non-increasing and `u ↦ u f(u)` is non-increasing; `PosAnti a` = nonnegative and
non-increasing. Sums, maxima, nonnegative multiples, `PosAnti × MonoU` products and nonempty products of `MonoU`
functions stay in `MonoU`. The building blocks are `(γ u - 1/2)⁻¹` (`MonoU` on `(u_min, ∞)`),
`γ + 1/(2u)` and `1 + (γ u - 1/2)⁻¹` (`PosAnti`) and `u^{-k}`, `k ≥ 1` (`MonoU`). Then `mrF_mono`:
`F` is in `MonoU u_min` for every `s ≥ 2`.
-/

namespace GeoSeq

open Finset

/-! ## The function classes -/

/-- Nonnegative and non-increasing on `(a, ∞)`. -/
def PosAnti (a : ℝ) (f : ℝ → ℝ) : Prop := (∀ u, a < u → 0 ≤ f u) ∧ AntitoneOn f (Set.Ioi a)

/-- Nonnegative, non-increasing, and `u ↦ u f(u)` non-increasing on `(a, ∞)` (`lem:MRbound`). -/
def MonoU (a : ℝ) (f : ℝ → ℝ) : Prop := PosAnti a f ∧ AntitoneOn (fun u => u * f u) (Set.Ioi a)

variable {a : ℝ}

lemma PosAnti.const {c : ℝ} (hc : 0 ≤ c) : PosAnti a (fun _ => c) :=
  ⟨fun _ _ => hc, fun _ _ _ _ _ => le_rfl⟩

lemma PosAnti.mul {f g : ℝ → ℝ} (hf : PosAnti a f) (hg : PosAnti a g) : PosAnti a (fun u => f u * g u) :=
  ⟨fun u hu => mul_nonneg (hf.1 u hu) (hg.1 u hu), fun x hx y hy hxy =>
    mul_le_mul (hf.2 hx hy hxy) (hg.2 hx hy hxy) (hg.1 y hy) (hf.1 x hx)⟩

lemma PosAnti.add {f g : ℝ → ℝ} (hf : PosAnti a f) (hg : PosAnti a g) : PosAnti a (fun u => f u + g u) :=
  ⟨fun u hu => add_nonneg (hf.1 u hu) (hg.1 u hu), fun x hx y hy hxy =>
    add_le_add (hf.2 hx hy hxy) (hg.2 hx hy hxy)⟩

lemma PosAnti.prod {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ S, PosAnti a (f i)) :
    PosAnti a (fun u => ∏ i ∈ S, f i u) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PosAnti.const (a := a) zero_le_one
  | insert i S hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hf i (mem_insert_self i S)).mul (ih fun j hj => hf j (mem_insert_of_mem hj))

lemma PosAnti.congr {f g : ℝ → ℝ} (hf : PosAnti a f) (h : ∀ u, a < u → g u = f u) : PosAnti a g :=
  ⟨fun u hu => (h u hu).symm ▸ hf.1 u hu, fun x hx y hy hxy => by
    rw [h x hx, h y hy]; exact hf.2 hx hy hxy⟩

lemma MonoU.congr {f g : ℝ → ℝ} (hf : MonoU a f) (h : ∀ u, a < u → g u = f u) : MonoU a g :=
  ⟨hf.1.congr h, fun x hx y hy hxy => by
    simp only; rw [h x hx, h y hy]; exact hf.2 hx hy hxy⟩

lemma MonoU.zero : MonoU a (fun _ => 0) :=
  ⟨PosAnti.const le_rfl, fun _ _ _ _ _ => by simp⟩

lemma MonoU.add {f g : ℝ → ℝ} (hf : MonoU a f) (hg : MonoU a g) : MonoU a (fun u => f u + g u) :=
  ⟨hf.1.add hg.1, fun x hx y hy hxy => by
    simp only [mul_add]; exact add_le_add (hf.2 hx hy hxy) (hg.2 hx hy hxy)⟩

lemma MonoU.const_mul {f : ℝ → ℝ} (hf : MonoU a f) {c : ℝ} (hc : 0 ≤ c) : MonoU a (fun u => c * f u) :=
  ⟨(PosAnti.const hc).mul hf.1, fun x hx y hy hxy => by
    simp only [mul_left_comm _ c]; exact mul_le_mul_of_nonneg_left (hf.2 hx hy hxy) hc⟩

lemma MonoU.mul_left (ha : 0 ≤ a) {f g : ℝ → ℝ} (hf : PosAnti a f) (hg : MonoU a g) :
    MonoU a (fun u => f u * g u) :=
  ⟨hf.mul hg.1, fun x hx y hy hxy => by
    simp only [mul_left_comm _ (f _)]
    exact mul_le_mul (hf.2 hx hy hxy) (hg.2 hx hy hxy)
      (mul_nonneg (ha.trans (le_of_lt hy)) (hg.1.1 y hy)) (hf.1 x hx)⟩

lemma MonoU.max (ha : 0 ≤ a) {f g : ℝ → ℝ} (hf : MonoU a f) (hg : MonoU a g) :
    MonoU a (fun u => max (f u) (g u)) := by
  refine ⟨⟨fun u hu => le_max_of_le_left (hf.1.1 u hu), fun x hx y hy hxy =>
    max_le_max (hf.1.2 hx hy hxy) (hg.1.2 hx hy hxy)⟩, fun x hx y hy hxy => ?_⟩
  have hx0 : 0 ≤ x := ha.trans (le_of_lt hx)
  have hy0 : 0 ≤ y := ha.trans (le_of_lt hy)
  simp only [mul_max_of_nonneg _ _ hx0, mul_max_of_nonneg _ _ hy0]
  exact max_le_max (hf.2 hx hy hxy) (hg.2 hx hy hxy)

lemma MonoU.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ S, MonoU a (f i)) :
    MonoU a (fun u => ∑ i ∈ S, f i u) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (MonoU.zero (a := a))
  | insert i S hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (mem_insert_self i S)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

lemma MonoU.prod (ha : 0 ≤ a) {ι : Type*} [DecidableEq ι] (S : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ S)
    {f : ι → ℝ → ℝ} (hf₀ : MonoU a (f i₀)) (hf : ∀ i ∈ S, PosAnti a (f i)) :
    MonoU a (fun u => ∏ i ∈ S, f i u) := by
  have h := MonoU.mul_left ha (PosAnti.prod (S.erase i₀) fun i hi => hf i (mem_of_mem_erase hi)) hf₀
  refine h.congr fun u _ => ?_
  rw [← Finset.prod_erase_mul S _ hi₀]

lemma MonoU.sup' (ha : 0 ≤ a) {ι : Type*} (S : Finset ι) (hS : S.Nonempty) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ S, MonoU a (f i)) : MonoU a (fun u => S.sup' hS (fun i => f i u)) := by
  refine ⟨⟨fun u hu => ?_, fun x hx y hy hxy => ?_⟩, fun x hx y hy hxy => ?_⟩
  · obtain ⟨i, hi⟩ := hS
    exact (hf i hi).1.1 u hu |>.trans (Finset.le_sup' (fun i => f i u) hi)
  · exact Finset.sup'_le _ _ fun i hi => ((hf i hi).1.2 hx hy hxy).trans (Finset.le_sup' (fun i => f i x) hi)
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hS (fun i => f i y)
    simp only
    rw [he]
    exact ((hf i hi).2 hx hy hxy).trans
      (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => f i x) hi) (ha.trans (le_of_lt hx)))

lemma MonoU.toPosAnti {f : ℝ → ℝ} (hf : MonoU a f) : PosAnti a f := hf.1

/-! ## Building blocks -/

/-- `(γ u - 1/2)⁻¹` is in `MonoU a` when `γ a ≥ 1/2`, `γ > 0`. -/
lemma monoU_inv_sub {γ : ℝ} (hγ : 0 < γ) (ha : 1 / 2 ≤ γ * a) :
    MonoU a (fun u => (γ * u - 1 / 2)⁻¹) := by
  have hpos : ∀ u, a < u → 0 < γ * u - 1 / 2 := fun u hu => by nlinarith
  refine ⟨⟨fun u hu => (inv_pos.2 (hpos u hu)).le, fun x hx y hy hxy => ?_⟩, fun x hx y hy hxy => ?_⟩
  · exact inv_anti₀ (hpos x hx) (by nlinarith)
  · simp only
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (hpos y hy) (hpos x hx)]
    nlinarith

/-- `γ + 1/(2u)` is in `PosAnti a` (`a ≥ 0`, `γ ≥ 0`). -/
lemma posAnti_add_inv {γ : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a) : PosAnti a (fun u => γ + 1 / (2 * u)) := by
  refine ⟨fun u hu => add_nonneg hγ (by have : 0 < u := lt_of_le_of_lt ha hu; positivity),
    fun x hx y hy hxy => ?_⟩
  have hx0 : 0 < x := lt_of_le_of_lt ha hx
  simp only
  gcongr

/-- `u^{-k}` (`k ≥ 1`) is in `MonoU a` (`a ≥ 0`). -/
lemma monoU_inv_pow (ha : 0 ≤ a) {k : ℕ} (hk : 1 ≤ k) : MonoU a (fun u => 1 / u ^ k) := by
  have hpos : ∀ u, a < u → 0 < u := fun u hu => lt_of_le_of_lt ha hu
  refine ⟨⟨fun u hu => by have := hpos u hu; positivity, fun x hx y hy hxy => ?_⟩, fun x hx y hy hxy => ?_⟩
  · have := hpos x hx; simp only; gcongr
  · have hx0 := hpos x hx
    have hy0 := hpos y hy
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only
    rw [pow_succ, pow_succ, mul_one_div, mul_one_div, div_mul_cancel_right₀ hy0.ne',
      div_mul_cancel_right₀ hx0.ne']
    gcongr

/-! ## The constants -/

theorem mrGamma_pos (s t : ℕ) (hs : 2 ≤ s) (ht1 : 1 ≤ t) (ht : t ≤ s - 1) : 0 < mrGamma s t := by
  unfold mrGamma
  have h1 : (0 : ℚ) ≤ ∑ j ∈ Ioc t (s - 1), (mrMu s t j : ℚ) / mrMu s (t - 1) j :=
    sum_nonneg fun j _ => by positivity
  have h2 : (0 : ℚ) < (mrG s : ℚ) / mrMu s (t - 1) t := by
    have := mrG_pos s hs
    have := mrMu_pos s (t - 1) t (by omega) ht
    positivity
  linarith

theorem mrMuBar_pos' (s c j : ℕ) (hs : 2 ≤ s) (hcj : c < j) (hj : j < s) : 1 ≤ mrMuBar s c j :=
  mrMuBar_pos s c j hs hcj hj

theorem mrQss_pos (s : ℕ) (hs : 2 ≤ s) : 0 < mrQss s := by
  unfold mrQss
  have h1 := mrMuBar_pos s 0 (s - 1) hs (by omega) (by omega)
  have h2 : (0 : ℚ) < ∏ t ∈ Ioc 0 (s - 1), mrGamma s t :=
    prod_pos fun t ht => mrGamma_pos s t hs (mem_Ioc.mp ht).1 (mem_Ioc.mp ht).2
  have h3 : (0 : ℚ) < ((mrMu s 0 (s - 1) / mrG s : ℕ) : ℚ) := by exact_mod_cast h1
  positivity

theorem mrUmin_ge (s t : ℕ) (hs : 2 ≤ s) (ht1 : 1 ≤ t) (ht : t ≤ s - 1) :
    1 / (2 * mrGamma s t) ≤ mrUmin s := by
  have hne : (Ioc 0 (s - 1)).Nonempty := ⟨1, mem_Ioc.mpr ⟨by omega, by omega⟩⟩
  unfold mrUmin
  rw [dite_eq_left_of_eq_true (eq_true hne)]
  exact Finset.le_sup' (fun t => 1 / (2 * mrGamma s t)) (mem_Ioc.mpr ⟨by omega, ht⟩)

theorem mrUmin_pos (s : ℕ) (hs : 2 ≤ s) : 0 < mrUmin s := by
  have h := mrUmin_ge s 1 hs le_rfl (by omega)
  have := mrGamma_pos s 1 hs le_rfl (by omega)
  exact lt_of_lt_of_le (by positivity) h

/-- `γ_t u_min ≥ 1/2` (so `γ_t u - 1/2 > 0` for `u > u_min`). -/
theorem mrGamma_umin (s t : ℕ) (hs : 2 ≤ s) (ht1 : 1 ≤ t) (ht : t ≤ s - 1) :
    (1 : ℝ) / 2 ≤ (mrGamma s t : ℝ) * (mrUmin s : ℝ) := by
  have h := mrUmin_ge s t hs ht1 ht
  have hg := mrGamma_pos s t hs ht1 ht
  have : (1 : ℚ) / 2 ≤ mrGamma s t * mrUmin s := by
    rw [div_le_iff₀ (by positivity)] at h; linarith
  have h' : (((1 : ℚ) / 2 : ℚ) : ℝ) ≤ ((mrGamma s t * mrUmin s : ℚ) : ℝ) := Rat.cast_le.mpr this
  push_cast at h'
  exact h'

/-! ## `F` and `u F(u)` are non-increasing (`lem:MRbound`, second part) -/

section FMono

variable (s : ℕ)

/-- `ν^+_{cj}/p(u)` factorized: `(μ̄/Q^s) ∏ (γ_i + 1/(2u)) · u^{-(s-(j-c))}`. -/
lemma nuP_div_pu (c j : ℕ) (hcj : c ≤ j) (hjs : j - c ≤ s) {u : ℝ} (hu : 0 < u) (hQ : (0 : ℝ) < mrQss s) :
    mrNuP s c j u / mrPu s u = ((mrMuBar s c j : ℝ) / (mrQss s : ℝ) *
      ∏ i ∈ Ioc c j, ((mrGamma s i : ℝ) + 1 / (2 * u))) * (1 / u ^ (s - (j - c))) := by
  unfold mrNuP mrPu
  have h1 : ∏ i ∈ Ioc c j, ((mrGamma s i : ℝ) * u + 1 / 2) =
      u ^ (j - c) * ∏ i ∈ Ioc c j, ((mrGamma s i : ℝ) + 1 / (2 * u)) := by
    rw [← Nat.card_Ioc c j, ← prod_const, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    field_simp
  have h2 : u ^ s = u ^ (j - c) * u ^ (s - (j - c)) := by rw [← pow_add, Nat.add_sub_cancel' hjs]
  rw [h1, h2]
  generalize ∏ i ∈ Ioc c j, ((mrGamma s i : ℝ) + 1 / (2 * u)) = P
  field_simp

/-- `1/ν^-_{rj}(u) = μ̄^{-1} ∏ (γ_i u - 1/2)⁻¹`. -/
lemma one_div_nuM (r j : ℕ) (u : ℝ) :
    1 / mrNuM s r j u = 1 / (mrMuBar s r j : ℝ) * ∏ i ∈ Ioc r j, ((mrGamma s i : ℝ) * u - 1 / 2)⁻¹ := by
  unfold mrNuM
  simp only [one_div, mul_inv, prod_inv_distrib]

/-- `η_{c-1}(j) ν^+_{cj}/2` factorized (`c ≥ 1`, `c ≤ j < s`, `u > u_min`). -/
lemma eta_nuP (hs : 2 ≤ s) (c j : ℕ) (hc : 1 ≤ c) (hcj : c ≤ j) (hj : j < s) {u : ℝ}
    (hu : (mrUmin s : ℝ) < u) :
    mrEta s (c - 1) j u * mrNuP s c j u / 2 = ∑ r ∈ range c,
      (mrMuBar s c j : ℝ) / (2 * (mrMuBar s r j : ℝ)) *
        ((∏ i ∈ Ioc c j, (1 + ((mrGamma s i : ℝ) * u - 1 / 2)⁻¹)) *
          ∏ i ∈ Ioc r c, ((mrGamma s i : ℝ) * u - 1 / 2)⁻¹) := by
  have hd : ∀ i, 1 ≤ i → i ≤ s - 1 → 0 < (mrGamma s i : ℝ) * u - 1 / 2 := fun i h1 h2 => by
    have := mrGamma_umin s i hs h1 h2
    have := mrGamma_pos s i hs h1 h2
    have : (0 : ℝ) < mrGamma s i := by exact_mod_cast this
    nlinarith
  unfold mrEta
  rw [Nat.sub_add_cancel hc, sum_mul, sum_div]
  refine sum_congr rfl fun r hr => ?_
  have hrc : r < c := mem_range.mp hr
  have hmr : (0 : ℝ) < mrMuBar s r j := by exact_mod_cast (mrMuBar_pos' s r j hs (by omega) hj)
  set d : ℕ → ℝ := fun i => (mrGamma s i : ℝ) * u - 1 / 2 with hdd
  have hPD : 0 < ∏ i ∈ Ioc c j, d i :=
    prod_pos fun i hi => hd i (by have := (mem_Ioc.mp hi).1; omega) (by have := (mem_Ioc.mp hi).2; omega)
  have hPR : 0 < ∏ i ∈ Ioc r c, d i :=
    prod_pos fun i hi => hd i (by have := (mem_Ioc.mp hi).1; omega) (by have := (mem_Ioc.mp hi).2; omega)
  have hA : ∏ i ∈ Ioc c j, ((mrGamma s i : ℝ) * u + 1 / 2) =
      (∏ i ∈ Ioc c j, (1 + (d i)⁻¹)) * ∏ i ∈ Ioc c j, d i := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    have := hd i (by have := (mem_Ioc.mp hi).1; omega) (by have := (mem_Ioc.mp hi).2; omega)
    rw [add_mul, inv_mul_cancel₀ this.ne']
    simp only [hdd]; ring
  have hM : mrNuM s r j u = (mrMuBar s r j : ℝ) * ((∏ i ∈ Ioc r c, d i) * ∏ i ∈ Ioc c j, d i) := by
    unfold mrNuM; rw [prod_Ioc_consecutive _ hrc.le hcj]
  unfold mrNuP
  rw [hM, hA, prod_inv_distrib]
  generalize ∏ i ∈ Ioc c j, (1 + (d i)⁻¹) = PA at *
  generalize ∏ i ∈ Ioc c j, d i = PD at *
  generalize ∏ i ∈ Ioc r c, d i = PR at *
  field_simp

/-- **`F` is in the class `MonoU u_min`**: nonnegative, non-increasing, and `u F(u)` non-increasing on
`(u_min, ∞)` (`lem:MRbound`, second part). -/
theorem mrF_mono (hs : 2 ≤ s) : MonoU (mrUmin s : ℝ) (fun u => mrF s u) := by
  have ha : (0 : ℝ) ≤ mrUmin s := by exact_mod_cast (mrUmin_pos s hs).le
  have hQ : (0 : ℝ) < mrQss s := by exact_mod_cast mrQss_pos s hs
  have hupos : ∀ u, (mrUmin s : ℝ) < u → 0 < u := fun u hu => lt_of_le_of_lt ha hu
  have hgam : ∀ i, 1 ≤ i → i ≤ s - 1 → (0 : ℝ) < mrGamma s i := fun i h1 h2 => by
    exact_mod_cast mrGamma_pos s i hs h1 h2
  -- blocks
  have hD : ∀ i, 1 ≤ i → i ≤ s - 1 →
      MonoU (mrUmin s : ℝ) (fun u => ((mrGamma s i : ℝ) * u - 1 / 2)⁻¹) := fun i h1 h2 =>
    monoU_inv_sub (hgam i h1 h2) (mrGamma_umin s i hs h1 h2)
  have hE1 : ∀ c j, c < j → j < s →
      MonoU (mrUmin s : ℝ) (fun u => mrNuP s c j u / mrPu s u) := by
    intro c j hcj hj
    have hk : 1 ≤ s - (j - c) := by omega
    refine (MonoU.mul_left ha ((PosAnti.const (c := (mrMuBar s c j : ℝ) / (mrQss s : ℝ)) (by positivity)).mul
      (PosAnti.prod (Ioc c j) fun i hi =>
      posAnti_add_inv (hgam i (by have := (mem_Ioc.mp hi).1; omega)
        (by have := (mem_Ioc.mp hi).2; omega)).le ha)) (monoU_inv_pow ha hk)).congr fun u hu => ?_
    exact nuP_div_pu s c j hcj.le (by omega) (hupos u hu) hQ
  have hE2 : ∀ r j, r < j → j < s → MonoU (mrUmin s : ℝ) (fun u => 1 / mrNuM s r j u) := by
    intro r j hrj hj
    have hm : (0 : ℝ) < mrMuBar s r j := by exact_mod_cast (mrMuBar_pos' s r j hs hrj hj)
    refine ((MonoU.prod ha (Ioc r j) (r + 1) (mem_Ioc.mpr ⟨by omega, by omega⟩)
      (hD (r + 1) (by omega) (by omega)) fun i hi =>
        (hD i (by have := (mem_Ioc.mp hi).1; omega) (by have := (mem_Ioc.mp hi).2; omega)).toPosAnti).const_mul
      (by positivity : (0 : ℝ) ≤ 1 / (mrMuBar s r j : ℝ))).congr fun u _ => ?_
    exact one_div_nuM s r j u
  have hE3 : ∀ c j, 1 ≤ c → c < j → j < s →
      MonoU (mrUmin s : ℝ) (fun u => mrEta s (c - 1) j u * mrNuP s c j u / 2) := by
    intro c j hc hcj hj
    refine (MonoU.sum (range c) fun r hr => ?_).congr fun u hu => eta_nuP s hs c j hc hcj.le hj hu
    have hrc : r < c := mem_range.mp hr
    have hm : (0 : ℝ) < mrMuBar s r j := by exact_mod_cast (mrMuBar_pos' s r j hs (by omega) hj)
    refine MonoU.const_mul ?_ (by positivity)
    refine MonoU.mul_left ha (PosAnti.prod (Ioc c j) fun i hi => (PosAnti.const zero_le_one).add
      (hD i (by have := (mem_Ioc.mp hi).1; omega) (by have := (mem_Ioc.mp hi).2; omega)).toPosAnti) ?_
    exact MonoU.prod ha (Ioc r c) (r + 1) (mem_Ioc.mpr ⟨by omega, by omega⟩)
      (hD (r + 1) (by omega) (by omega)) fun i hi =>
        (hD i (by have := (mem_Ioc.mp hi).1; omega) (by have := (mem_Ioc.mp hi).2; omega)).toPosAnti
  have hrow : ∀ c ∈ range s, MonoU (mrUmin s : ℝ) (fun u => mrFrow s c u) := by
    intro c hc
    have hcs := mem_range.mp hc
    by_cases h0 : c = 0
    · subst h0
      have hs1 : 1 ≤ s := by omega
      refine (((MonoU.sum (Ioo 0 s) fun j hj => hE1 0 j (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2).const_mul
        (by norm_num : (0 : ℝ) ≤ 2)).add ((monoU_inv_pow ha hs1).const_mul
          (by positivity : (0 : ℝ) ≤ 1 / (mrQss s : ℝ)))).congr fun u hu => ?_
      have hu0 := hupos u hu
      unfold mrFrow
      rw [ite_eq_left_of_eq_true _ _ (eq_self 0), add_div, mul_div_assoc, sum_div]
      unfold mrPu
      rw [one_div_mul_one_div]
    · refine ((MonoU.sum (Ioo c s) fun j hj => MonoU.max ha (hE1 c j (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2)
        (hE3 c j (by omega) (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2)).const_mul (by norm_num : (0 : ℝ) ≤ 2) |>.add
        (MonoU.sum (range c) fun r hr => hE2 r c (mem_range.mp hr) hcs)).congr fun u _ => ?_
      unfold mrFrow
      rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      unfold mrEta
      rw [Nat.sub_add_cancel (by omega)]
  have hne : (range s).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  refine (MonoU.sup' ha (range s) hne hrow).congr fun u _ => ?_
  unfold mrF
  rw [dite_eq_left_of_eq_true (eq_true hne)]

end FMono

end GeoSeq
