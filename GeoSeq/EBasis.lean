/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S11Series
public import GeoSeq.DualPoly

@[expose] public section

/-!
# GeoSeq stage S11: the e-basis and the law of an arbitrary scramble (`lem:residue`, `lem:ebasis`)

* Triangular families of functionals: `tri_mem_span` (a family `f_n = ∑_{i ≤ n} A[n][i] τ_i` with
  `A[n][n] ≠ 0` spans every `τ_i`, `i ≤ n`), hence the matrices `B_c` (`ebas_B_exists`: the e-basis in the
  rows of the scramble) and `T_c` (`ebas_T_exists`: the rows in the e-basis) exist; they are unique
  (`ebas_indep`, `scrDig_det`).
* **`residue_faure`** (`lem:residue`, `s = 2`): the law of an arbitrary scramble at level `K` from the
  decompositions of the form `Φ_K^{(c)}`.
* **`ebasis`** (`lem:ebasis`): the law of an arbitrary scramble in the e-basis, both coordinates.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-! ## Triangular families of functionals -/

section Tri

variable (τ f : ℕ → F[X] → F)

/-- The span of `f_0, …, f_n` in the space of functionals. -/
def triSpan (n : ℕ) : Submodule F (F[X] → F) :=
  Submodule.span F (Set.range fun j : Fin (n + 1) => f j)

lemma triSpan_mono {n m : ℕ} (h : n ≤ m) : triSpan f n ≤ triSpan f m := by
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨Fin.castLE (by omega) j, rfl⟩

lemma f_mem_triSpan (n : ℕ) : f n ∈ triSpan f n :=
  Submodule.subset_span ⟨Fin.last n, rfl⟩

/-- A lower-triangular family with nonzero diagonal spans every `τ_i`, `i ≤ n`. -/
lemma tri_mem_span (A : ℕ → ℕ → F) (hA : ∀ n, A n n ≠ 0)
    (hf : ∀ n V, f n V = ∑ i ∈ range (n + 1), A n i * τ i V) (i : ℕ) : τ i ∈ triSpan f i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have he : τ i = (A i i)⁻¹ • (f i - ∑ k ∈ range i, A i k • τ k) := by
      funext V
      simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, hf i V,
        Finset.sum_range_succ]
      field_simp [hA i]
      ring
    rw [he]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (f_mem_triSpan f i) ?_)
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
    exact triSpan_mono f (by simp at hk; omega) (ih k (by simpa using hk))

/-- Coefficients of an element of `triSpan f n`. -/
lemma triSpan_coef (n : ℕ) (g : F[X] → F) (hg : g ∈ triSpan f n) :
    ∃ β : ℕ → F, ∀ V, g V = ∑ j ∈ range (n + 1), β j * f j V := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hg
  refine ⟨fun j => if h : j < n + 1 then c ⟨j, h⟩ else 0, fun V => ?_⟩
  rw [← hc, Finset.sum_apply, ← Fin.sum_univ_eq_sum_range (fun j =>
    (if h : j < n + 1 then c ⟨j, h⟩ else 0) * f j V)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [j.isLt]

/-- **Change of triangular basis**: a functional `g = ∑_{i ≤ n} G_i τ_i` is a combination of
`f_0, …, f_n`. -/
lemma tri_expand (A : ℕ → ℕ → F) (hA : ∀ n, A n n ≠ 0)
    (hf : ∀ n V, f n V = ∑ i ∈ range (n + 1), A n i * τ i V) (n : ℕ) (g : F[X] → F) (G : ℕ → F)
    (hg : ∀ V, g V = ∑ i ∈ range (n + 1), G i * τ i V) :
    ∃ β : ℕ → F, ∀ V, g V = ∑ j ∈ range (n + 1), β j * f j V := by
  refine triSpan_coef f n g ?_
  have : g = ∑ i ∈ range (n + 1), G i • τ i := by
    funext V; simp [hg V]
  rw [this]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact triSpan_mono f (by simp at hi; omega) (tri_mem_span τ f A hA hf i)

end Tri

/-! ## The Taylor-coefficient form of the two families -/

/-- `τ_{a,i}(V) = [(z-a)^i] V`. -/
noncomputable def tayl (a : F) (i : ℕ) (V : F[X]) : F := (Polynomial.taylor a V).coeff i

lemma scrDig_tayl (a : F) (L : ℕ → ℕ → F) (n : ℕ) (V : F[X]) :
    scrDig a L n V = ∑ i ∈ range (n + 1), L n i * tayl a i V := rfl

lemma faureDel_sq (c : Fin 2) : faureDel c * faureDel c = (1 : F) := by
  fin_cases c <;> simp [faureDel]

lemma faureDel_ne (c : Fin 2) : faureDel c ≠ (0 : F) := by
  intro h; have := faureDel_sq (F := F) c; rw [h, zero_mul] at this; exact zero_ne_one this

/-- The e-basis in Taylor coefficients: `ε_{c,j} = ∑_{i ≤ j} [t^{j-i}](t + δ)^{-j-2} · τ_i`. -/
lemma ebas_tayl (c : Fin 2) (j : ℕ) (V : F[X]) :
    ebas c j V = ∑ i ∈ range (j + 1),
      coeff (j - i) (((X + C (faureDel c) : PS) ^ (j + 2))⁻¹) * tayl (faurePl c) i V := by
  rw [ebas, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i k => coeff i (Polynomial.taylor (faurePl c) V : PS) *
      coeff k (((X + C (faureDel c) : PS) ^ (j + 2))⁻¹))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_coe, tayl, mul_comm]

lemma ebas_diag (c : Fin 2) (j : ℕ) :
    coeff (j - j) (((X + C (faureDel c) : PS) ^ (j + 2))⁻¹) ≠ 0 := by
  rw [Nat.sub_self, coeff_inv_pow _ (faureDel_sq c) _ _ (by omega)]
  simp [faureDel_ne c]

/-- **The matrices `B_c`** (`app:machinery`): `ε_{c,i} = ∑_{j ≤ i} B_c[i][j] y_{c,j}`. -/
theorem ebas_B_exists (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) :
    ∃ B : Fin 2 → ℕ → ℕ → F, ∀ c i V,
      ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V := by
  have h : ∀ c i, ∃ β : ℕ → F, ∀ V,
      ebas c i V = ∑ j ∈ range (i + 1), β j * scrDig (faurePl c) (L c) j V := fun c i =>
    tri_expand (tayl (faurePl c)) (fun n V => scrDig (faurePl c) (L c) n V) (L c) (hL c)
      (fun n V => scrDig_tayl _ _ _ _) i (ebas c i) _ (ebas_tayl c i)
  choose B hB using h
  exact ⟨B, hB⟩

/-- **The matrices `T_c`** (`app:machinery`): `η_{c,n} ≡ ∑_{k ≤ n} T_c[n][k] e_{c,k}`, i.e.
`y_{c,n} = ∑_{k ≤ n} T_c[n][k] ε_{c,k}`. -/
theorem ebas_T_exists (L : Fin 2 → ℕ → ℕ → F) :
    ∃ T : Fin 2 → ℕ → ℕ → F, ∀ c n V,
      scrDig (faurePl c) (L c) n V = ∑ k ∈ range (n + 1), T c n k * ebas c k V := by
  have h : ∀ c n, ∃ β : ℕ → F, ∀ V,
      scrDig (faurePl c) (L c) n V = ∑ k ∈ range (n + 1), β k * ebas c k V := fun c n =>
    tri_expand (tayl (faurePl c)) (fun j V => ebas c j V)
      (fun j i => coeff (j - i) (((X + C (faureDel c) : PS) ^ (j + 2))⁻¹)) (ebas_diag c)
      (fun j V => ebas_tayl c j V) n _ _ (scrDig_tayl _ _ _)
  choose T hT using h
  exact ⟨T, hT⟩

/-! ## Uniqueness -/

lemma tayl_test (a : F) (i m : ℕ) :
    tayl a i ((Polynomial.X - Polynomial.C a) ^ m) = if i = m then 1 else 0 := by
  rw [tayl, taylor_X_sub_C_pow, Polynomial.coeff_X_pow]

/-- A triangular family with nonzero diagonal is linearly independent (tested on `(z-a)^m`). -/
lemma tri_indep (a : F) (f : ℕ → F[X] → F) (A : ℕ → ℕ → F) (hA : ∀ n, A n n ≠ 0)
    (hf : ∀ n V, f n V = ∑ i ∈ range (n + 1), A n i * tayl a i V) (n : ℕ) (d : ℕ → F)
    (hd : ∀ V, ∑ k ∈ range (n + 1), d k * f k V = 0) : ∀ k ≤ n, d k = 0 := by
  classical
  by_contra hne
  push_neg at hne
  set S := (range (n + 1)).filter (fun k => d k ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨k, hk, hk0⟩ := hne
    exact ⟨k, by simp only [S, mem_filter, mem_range]; exact ⟨by omega, hk0⟩⟩
  set k0 := S.max' hS
  have hk0 : k0 ∈ S := S.max'_mem hS
  simp only [S, mem_filter, mem_range] at hk0
  have h := hd ((Polynomial.X - Polynomial.C a) ^ k0)
  rw [Finset.sum_eq_single k0] at h
  · rw [hf, Finset.sum_eq_single k0] at h
    · rw [tayl_test, ite_eq_left rfl, mul_one] at h
      exact (mul_ne_zero hk0.2 (hA k0)) h
    · intro i _ hi; rw [tayl_test, ite_eq_right hi, mul_zero]
    · intro h'; simp at h'
  · intro k hk hkk
    by_cases hdk : d k = 0
    · rw [hdk, zero_mul]
    · have hle : k ≤ k0 := S.le_max' k (by simp [S]; exact ⟨by simpa using hk, hdk⟩)
      rw [hf, Finset.sum_eq_zero, mul_zero]
      intro i hi
      rw [tayl_test, ite_eq_right (by simp at hi; omega), mul_zero]
  · intro h'; simp at h'; omega

/-- The e-basis functionals are linearly independent: `T_c` is unique. -/
lemma ebas_indep (c : Fin 2) (n : ℕ) (d : ℕ → F)
    (hd : ∀ V, ∑ k ∈ range (n + 1), d k * ebas c k V = 0) : ∀ k ≤ n, d k = 0 :=
  tri_indep (faurePl c) (fun j V => ebas c j V) _ (ebas_diag c) (fun j V => ebas_tayl c j V) n d hd

/-- Two families related to the same `ε` by the same lower-triangular `B` with nonzero diagonal agree. -/
lemma tri_det (B : ℕ → ℕ → F) (hB : ∀ i, B i i ≠ 0) (e y y' : ℕ → F)
    (hy : ∀ i, e i = ∑ j ∈ range (i + 1), B i j * y j)
    (hy' : ∀ i, e i = ∑ j ∈ range (i + 1), B i j * y' j) (i : ℕ) : y i = y' i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have h := (hy i).symm.trans (hy' i)
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_congr rfl (fun j hj => by rw [ih j (by simpa using hj)])] at h
    exact mul_left_cancel₀ (hB i) (add_left_cancel h)

/-- `B_c[i][i] ≠ 0` (the diagonal of `B_c` is the inverse of the diagonal of `T_c`). -/
lemma B_diag_ne (L : Fin 2 → ℕ → ℕ → F) (B : Fin 2 → ℕ → ℕ → F)
    (hB : ∀ c i V, ebas c i V = ∑ j ∈ range (i + 1), B c i j * scrDig (faurePl c) (L c) j V)
    (c : Fin 2) (i : ℕ) : B c i i ≠ 0 := by
  intro h0
  have h := hB c i ((Polynomial.X - Polynomial.C (faurePl c)) ^ i)
  rw [ebas_tayl, Finset.sum_eq_single i, Finset.sum_eq_single i] at h
  · rw [h0, zero_mul, tayl_test, ite_eq_left rfl, mul_one] at h
    exact ebas_diag c i h
  · intro j hj hji
    rw [scrDig_tayl, Finset.sum_eq_zero, mul_zero]
    intro k hk; rw [tayl_test, ite_eq_right (by simp at hj hk; omega), mul_zero]
  · intro h'; simp at h'
  · intro j hj hji; rw [tayl_test, ite_eq_right hji, mul_zero]
  · intro h'; simp at h'

/-! ## The residue identity (`lem:residue`, `s = 2`) -/

lemma coeff_mul_tayl (a : F) (R : PS) (j : ℕ) (V : F[X]) :
    coeff j ((Polynomial.taylor a V : PS) * R) =
      ∑ i ∈ range (j + 1), coeff (j - i) R * tayl a i V := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i k => coeff i (Polynomial.taylor a V : PS) * coeff k R)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_coe, tayl, mul_comm]

lemma faurePl_zero : faurePl (0 : Fin 2) = (0 : F) := rfl
lemma faurePl_one : faurePl (1 : Fin 2) = (1 : F) := rfl
lemma faureDel_zero : faureDel (0 : Fin 2) = (-1 : F) := rfl
lemma faureDel_one : faureDel (1 : Fin 2) = (1 : F) := rfl

/-- **The residue theorem for `Φ_K^{(c)}`** (`lem:residue`): `Res_{a_0}(VΦ) + Res_{a_1}(VΦ) = 0` for
`deg V < 2K`, `K ≥ 1`. -/
theorem residue_thm (K : ℕ) (hK : 1 ≤ K) (c : Fin 2) (V : F[X]) (hV : V.natDegree < 2 * K) :
    resPhi K c 0 V + resPhi K c 1 V = 0 := by
  fin_cases c
  · simp only [resPhi, Fin.zero_eta, if_true, show ¬ ((1 : Fin 2) = 0) by decide, if_false,
      faurePl_zero, faurePl_one, faureDel_zero, faureDel_one]
    have h := residue2 (F := F) (K + 1) K (by omega) hK V (by omega)
    rwa [Nat.add_sub_cancel] at h
  · simp only [resPhi, Fin.mk_one, show ¬ ((0 : Fin 2) = 1) by decide, if_false, if_true,
      faurePl_zero, faurePl_one, faureDel_zero, faureDel_one]
    have h := residue2 (F := F) K (K + 1) hK (by omega) V (by omega)
    rwa [Nat.add_sub_cancel] at h

/-- **`lem:residue`** (`s = 2`, Faure frame): if `η_{c,K} ≡ λ Φ_K^{(c)} + ∑_{j<K} o_j η_{c,j}` at `a_c` and
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
  have hres := residue_thm K hK c V hV
  have hsum : resPhi K c c V = -resPhi K c c' V := by
    fin_cases c <;> fin_cases c' <;> simp_all <;> linear_combination hres
  rw [hown, hsum, hoth]; ring

/-- The decompositions of `lem:residue` exist, with `λ ≠ 0` (`K ≥ 1`, nonzero diagonal). -/
theorem residue_decomp (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (c c' : Fin 2) (hcc : c' ≠ c) :
    (∃ lam : F, lam ≠ 0 ∧ ∃ o : ℕ → F, ∀ V, scrDig (faurePl c) (L c) K V =
        lam * resPhi K c c V + ∑ j ∈ range K, o j * scrDig (faurePl c) (L c) j V) ∧
      ∃ ξ : ℕ → F, ∀ V, resPhi K c c' V = ∑ j ∈ range K, ξ j * scrDig (faurePl c') (L c') j V := by
  set δ := faureDel (F := F) c
  set R : PS := ((X + C δ) ^ K)⁻¹
  have hR0 : coeff 0 R = δ ^ K := by
    rw [coeff_inv_pow δ (faureDel_sq c) K 0 hK]; simp
  have hδK : δ ^ K * δ ^ K = 1 := by rw [← mul_pow, faureDel_sq c, one_pow]
  have hKK : range K = range (K - 1 + 1) := by rw [Nat.sub_add_cancel hK]
  refine ⟨⟨L c K K * δ ^ K, mul_ne_zero (hL c K) (pow_ne_zero _ (faureDel_ne c)), ?_⟩, ?_⟩
  · have hexp : ∀ V, scrDig (faurePl c) (L c) K V - L c K K * δ ^ K * resPhi K c c V =
        ∑ i ∈ range (K - 1 + 1), (L c K i - L c K K * δ ^ K * coeff (K - i) R) *
          tayl (faurePl c) i V := by
      intro V
      simp only [resPhi, if_true]
      rw [scrDig_tayl, coeff_mul_tayl, ← hKK, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_range_succ, Nat.sub_self, hR0]
      rw [show L c K K * δ ^ K * (δ ^ K * tayl (faurePl c) K V) =
        L c K K * tayl (faurePl c) K V by
          rw [show L c K K * δ ^ K * (δ ^ K * tayl (faurePl c) K V) =
            L c K K * (δ ^ K * δ ^ K) * tayl (faurePl c) K V by ring, hδK, mul_one], sub_self,
        add_zero]
      refine Finset.sum_congr rfl fun i _ => by ring
    obtain ⟨o, ho⟩ := tri_expand (tayl (faurePl c)) (fun n V => scrDig (faurePl c) (L c) n V)
      (L c) (hL c) (fun n V => scrDig_tayl _ _ _ _) (K - 1) _ _ hexp
    refine ⟨o, fun V => ?_⟩
    rw [hKK]
    linear_combination ho V
  · have hexp : ∀ V, resPhi K c c' V = ∑ i ∈ range (K - 1 + 1),
        coeff (K - 1 - i) (((X + C (faureDel c')) ^ (K + 1))⁻¹ : PS) * tayl (faurePl c') i V := by
      intro V
      simp only [resPhi, ite_eq_right hcc]
      exact coeff_mul_tayl _ _ _ _
    obtain ⟨ξ, hξ⟩ := tri_expand (tayl (faurePl c')) (fun n V => scrDig (faurePl c') (L c') n V)
      (L c') (hL c') (fun n V => scrDig_tayl _ _ _ _) (K - 1) _ _ hexp
    exact ⟨ξ, fun V => by rw [hKK]; exact hξ V⟩

/-! ## The law in the e-basis (`lem:ebasis`) -/

/-- The algebra of `lem:ebasis`: from the residue relation `∑_{n ≤ K} γ_n ε_own(K-n) + ε_oth(K-1) = 0`
and the expansions `ε = B y`, solve for `y_own(K)`. -/
lemma ebasis_alg (γ : ℕ → F) (hγ : γ 0 = 1) (Bo Bx : ℕ → ℕ → F) (yo yx eo ex : ℕ → F)
    (ho : ∀ i, eo i = ∑ j ∈ range (i + 1), Bo i j * yo j)
    (hx : ∀ i, ex i = ∑ j ∈ range (i + 1), Bx i j * yx j) (K : ℕ) (hK : 1 ≤ K) (hBK : Bo K K ≠ 0)
    (hres : ∑ n ∈ range (K + 1), γ n * eo (K - n) + ex (K - 1) = 0) :
    yo K = ∑ j ∈ range K, (-(∑ n ∈ range (K - j + 1), γ n * Bo (K - n) j) / Bo K K) * yo j +
      ∑ j ∈ range K, (-(Bx (K - 1) j) / Bo K K) * yx j := by
  have hswap : ∑ n ∈ range (K + 1), γ n * eo (K - n) =
      ∑ j ∈ range (K + 1), (∑ n ∈ range (K - j + 1), γ n * Bo (K - n) j) * yo j := by
    simp_rw [ho, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (t' := range (K + 1)) (s' := fun j => range (K - j + 1))]
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => by ring
    · intro n j; simp only [mem_range]; omega
  have hex : ex (K - 1) = ∑ j ∈ range K, Bx (K - 1) j * yx j := by
    rw [hx, Nat.sub_add_cancel hK]
  rw [hswap, hex, Finset.sum_range_succ, Nat.sub_self, zero_add, Finset.sum_range_one, hγ,
    one_mul, Nat.sub_zero] at hres
  have e1 : ∑ j ∈ range K, (-(∑ n ∈ range (K - j + 1), γ n * Bo (K - n) j) / Bo K K) * yo j =
      (-1 / Bo K K) * ∑ j ∈ range K, (∑ n ∈ range (K - j + 1), γ n * Bo (K - n) j) * yo j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j ∈ range K, (-(Bx (K - 1) j) / Bo K K) * yx j =
      (-1 / Bo K K) * ∑ j ∈ range K, Bx (K - 1) j * yx j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  field_simp
  linear_combination hres

/-- **`lem:ebasis`** (law of an arbitrary scramble of the Faure frame in the e-basis, both coordinates):
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
  refine ebasis_alg (fun n => coeff n (gamF : PS)) gamF_zero (B c) (B c') _ _
    (fun i => ebas c i V) (fun i => ebas c' i V) (fun i => hB c i V) (fun i => hB c' i V) K hK
    (B_diag_ne L B hB c K) ?_
  have hres := residue_thm K hK c V hV
  have hown : resPhi K c c V = ∑ n ∈ range (K + 1), coeff n (gamF : PS) * ebas c (K - n) V := by
    simp only [resPhi, if_true, ebas]
    exact gam_expand _ (faureDel_sq c) _ K
  have hoth : resPhi K c c' V = ebas c' (K - 1) V := by
    simp only [resPhi, ite_eq_right hcc, ebas, show K - 1 + 2 = K + 1 by omega]
  rw [← hown, ← hoth]
  fin_cases c <;> fin_cases c' <;> simp_all <;> linear_combination hres

end GeoSeq
