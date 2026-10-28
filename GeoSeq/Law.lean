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
# GeoSeq stage S3: the multi-digit law `prop:law`

The proof of the paper, in power-series form. Fix a self-similar scramble (`def:selfsim`,
`ssGen g zθ`), a polynomial `w` of degree `≤ s` with `w(z_c(θx)) = θx` for every `c` (`eq:roots`,
the local roots; `θ` a unit), and a right inverse `G` of the frame matrix `M = frameM g zθ`.

* `vecDigit_ss`: the digits of an index vector `V` are the coefficients of `g_c · V(z_c(θx))`.
* `lawPoly`: the index polynomial with prescribed `w`-adic digits `ν̃ = (G P) mod x^K` (`eq:wadic`
  read backwards: `V = ∑_{k<K} ∑_b ν̃_{k,b} θ^{-k} z^b w^k`, degree `< sK`).
* `law_digits`: its digit series are `Y = M ν̃ = P - M H` with `H = G P - ν̃ = O(x^K)`, so the cell
  digits are those of `P` and the geometric digit `K+i` is `[x^{K+i}]P - ∑_b ∑_{a≤i} M_a [x^{K+i-a}] G P`.
* `law_cells`: the cell-digit map `R^{sK} → R^{s×K}` is onto (by the construction), hence bijective for
  finite `R` (counting) — the `w`-adic expansion of an arbitrary `V` is not needed.
* **`law`**: `D_i(l)[c][c'] = lawD g zθ G i l c c'` for every level `K ≥ l` (K-independence).
* `law_first`: the first form `D_i(l) = [x^{l+i}] M_{>i} Ĝ`.
* `frame_inv`: the frame matrix of a frame (distinct places, `g_c(0) ≠ 0`, over a field) has an inverse.
* `cell_existsUnique`, `carry_exists`, `carryEntry_unique`: for ANY digital sequence whose prefix
  `P_{sK}` is a `(0,sK,s)`-net the carry responses exist and are unique (the bridge to `cert`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Matrix

variable {R : Type*} [CommRing R] {s : ℕ}

/-! ## Coefficient lemmas -/

/-- `[x^n] f/(1-x) = ∑_{t ≤ n} [x^t] f`. -/
lemma coeff_mul_mk_one (f : PowerSeries R) (n : ℕ) :
    coeff n (f * PowerSeries.mk 1) = ∑ t ∈ range (n + 1), coeff t f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a f * coeff b (PowerSeries.mk (1 : ℕ → R)))]
  simp

/-- The carry pattern of length `l` at level `K`, as a series: `[x^{K+j}] f · pat = Ĝ_{l+j} - Ĝ_j`. -/
lemma coeff_mul_pat (f : PowerSeries R) (K l j : ℕ) (hl : l ≤ K) :
    coeff (K + j) (f * PowerSeries.mk (fun n => if K - l ≤ n ∧ n < K then (1 : R) else 0)) =
      coeff (l + j) (f * PowerSeries.mk 1) - coeff j (f * PowerSeries.mk 1) := by
  rw [coeff_mul_mk_one, coeff_mul_mk_one, ← Finset.sum_Ico_eq_sub _ (by omega : j + 1 ≤ l + j + 1),
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a f * coeff b (PowerSeries.mk (fun n => if K - l ≤ n ∧ n < K then (1 : R) else 0)))]
  simp only [coeff_mk, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [mem_filter, mem_range, mem_Ico]
  omega

/-- The digits of an index vector of a self-similar scramble: `y_{c,n} = [x^n] g_c · V(z_c(θx))`. -/
theorem vecDigit_ss (g zθ : Fin s → PowerSeries R) {m : ℕ} (V : Fin m → R) (c : Fin s) (n : ℕ) :
    vecDigit (ssGen g zθ) V c n =
      coeff n (g c * ∑ k : Fin m, PowerSeries.C (V k) * zθ c ^ (k : ℕ)) := by
  simp only [vecDigit, ssGen, mul_sum, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, coeff_C_mul, mul_comm]

/-! ## The index polynomial with prescribed `w`-adic digits (`eq:wadic`) -/

/-- The index polynomial `V = ∑_b ∑_{k<K} [x^k](G P)_b · θ'^k · z^b w^k` (`θ' = θ^{-1}`): its `w`-adic
digits are `ν_{k,b} = θ^{-k} [x^k] (G P)_b`, so that `ν̃_b(x) = ν_b(θx) = (G P)_b mod x^K`. -/
noncomputable def lawPoly (w : Polynomial R) (θ' : R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (P : Fin s → PowerSeries R) (K : ℕ) : Polynomial R :=
  ∑ b : Fin s, ∑ k ∈ range K,
    Polynomial.C (coeff k ((G *ᵥ P) b) * θ' ^ k) * Polynomial.X ^ (b : ℕ) * w ^ k

/-- The index vector `V ∈ R^{sK}` of `lawPoly`. -/
noncomputable def lawVec (w : Polynomial R) (θ' : R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (P : Fin s → PowerSeries R) (K : ℕ) : Fin (s * K) → R :=
  fun k => (lawPoly w θ' G P K).coeff k

/-- `ν̃_b = (G P)_b mod x^K`. -/
noncomputable def lawNu (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (P : Fin s → PowerSeries R)
    (K : ℕ) (b : Fin s) : PowerSeries R :=
  PowerSeries.mk fun k => if k < K then coeff k ((G *ᵥ P) b) else 0

lemma lawPoly_natDegree (w : Polynomial R) (hw : w.natDegree ≤ s) (θ' : R)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (P : Fin s → PowerSeries R) (K : ℕ)
    (hs : 1 ≤ s) (hK : 1 ≤ K) : (lawPoly w θ' G P K).natDegree < s * K := by
  have hle : (lawPoly w θ' G P K).natDegree ≤ s * K - 1 := by
    unfold lawPoly
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hk' : k < K := mem_range.1 hk
    have hb := b.isLt
    calc _ ≤ (Polynomial.C (coeff k ((G *ᵥ P) b) * θ' ^ k) * Polynomial.X ^ (b : ℕ)).natDegree +
          (w ^ k).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (b : ℕ) + k * s := by
          gcongr
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
          · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ hw)
      _ ≤ s * K - 1 := by
          have : k * s + s ≤ s * K := by
            rw [mul_comm s K, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk'
          omega
  have : 1 ≤ s * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  omega

lemma sum_C_X_pow (f : PowerSeries R) (K : ℕ) :
    ∑ k ∈ range K, PowerSeries.C (coeff k f) * X ^ k =
      PowerSeries.mk fun k => if k < K then coeff k f else 0 := by
  ext n
  rw [map_sum, coeff_mk]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [mem_range]

/-- Substituting the local root: `V(z_c(θx)) = ∑_b z_c(θx)^b ν̃_b(x)`. -/
lemma lawPoly_aeval (w : Polynomial R) (θ θ' : R) (hθ : θ * θ' = 1)
    (zθ : Fin s → PowerSeries R) (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (P : Fin s → PowerSeries R) (K : ℕ) (c : Fin s) :
    Polynomial.aeval (zθ c) (lawPoly w θ' G P K) = ∑ b : Fin s, zθ c ^ (b : ℕ) * lawNu G P K b := by
  unfold lawPoly lawNu
  simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hroot c,
    PowerSeries.algebraMap_eq]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_C_X_pow, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  calc PowerSeries.C (coeff k ((G *ᵥ P) b)) * PowerSeries.C θ' ^ k * zθ c ^ (b : ℕ) *
        (PowerSeries.C θ * X) ^ k
      = zθ c ^ (b : ℕ) * (PowerSeries.C (coeff k ((G *ᵥ P) b)) * X ^ k) *
          (PowerSeries.C θ' * PowerSeries.C θ) ^ k := by ring
    _ = _ := by rw [← map_mul, mul_comm θ' θ, hθ, map_one, one_pow, mul_one]

/-! ## The digits of the constructed index vector -/

/-- **The level-`K` law of a self-similar scramble, constructively** (proof of `prop:law`): for any
target series `P`, the index vector `lawVec` has digit series `Y = M ν̃ = P - M H`, `H = G P - ν̃`:
its cell digits (`n < K`) are those of `P`, and its geometric digit `K+i` is
`[x^{K+i}] P_c - ∑_b ∑_{a ≤ i} [x^a] M[c][b] · [x^{K+i-a}] (G P)_b`. -/
theorem law_digits (g zθ : Fin s → PowerSeries R) (w : Polynomial R) (hw : w.natDegree ≤ s)
    (θ θ' : R) (hθ : θ * θ' = 1)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (hMG : frameM g zθ * G = 1)
    (P : Fin s → PowerSeries R) (K : ℕ) (hK : 1 ≤ K) (c : Fin s) :
    (∀ n < K, vecDigit (ssGen g zθ) (lawVec w θ' G P K) c n = coeff n (P c)) ∧
    ∀ i, vecDigit (ssGen g zθ) (lawVec w θ' G P K) c (K + i) =
      coeff (K + i) (P c) - ∑ b, ∑ a ∈ range (i + 1),
        coeff a (frameM g zθ c b) * coeff (K + i - a) ((G *ᵥ P) b) := by
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.2 (Fin.pos c).ne'
  set H : Fin s → PowerSeries R := G *ᵥ P - lawNu G P K with hHdef
  have hY : ∀ n, vecDigit (ssGen g zθ) (lawVec w θ' G P K) c n =
      coeff n ((frameM g zθ *ᵥ lawNu G P K) c) := by
    intro n
    rw [vecDigit_ss]
    have e : ∑ k : Fin (s * K), PowerSeries.C (lawVec w θ' G P K k) * zθ c ^ (k : ℕ) =
        Polynomial.aeval (zθ c) (lawPoly w θ' G P K) := by
      rw [Polynomial.aeval_eq_sum_range' (lawPoly_natDegree w hw θ' G P K hs hK),
        ← Fin.sum_univ_eq_sum_range (fun i => (lawPoly w θ' G P K).coeff i • zθ c ^ i)]
      simp [lawVec, smul_eq_C_mul]
    rw [e, lawPoly_aeval w θ θ' hθ zθ hroot G P K c, mul_sum]
    simp only [Matrix.mulVec, dotProduct, frameM, mul_assoc]
  have hdec : frameM g zθ *ᵥ lawNu G P K = P - frameM g zθ *ᵥ H := by
    rw [hHdef, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMG, Matrix.one_mulVec, sub_sub_cancel]
  have hH : ∀ b n, coeff n (H b) = if n < K then 0 else coeff n ((G *ᵥ P) b) := by
    intro b n
    simp only [hHdef, Pi.sub_apply, map_sub, lawNu, coeff_mk]
    split_ifs <;> simp
  have hMH : ∀ n, coeff n ((frameM g zθ *ᵥ H) c) = ∑ b, ∑ a ∈ range (n + 1),
      coeff a (frameM g zθ c b) * (if n - a < K then 0 else coeff (n - a) ((G *ᵥ P) b)) := by
    intro n
    show coeff n (∑ b, frameM g zθ c b * H b) = _
    rw [map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a a' => coeff a (frameM g zθ c b) * coeff a' (H b))]
    simp only [hH, Nat.succ_eq_add_one]
  refine ⟨fun n hn => ?_, fun i => ?_⟩
  · rw [hY, hdec, Pi.sub_apply, map_sub, hMH]
    have : ∀ a, n - a < K := fun a => by omega
    simp [this]
  · rw [hY, hdec, Pi.sub_apply, map_sub, hMH]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [show K + i + 1 = (i + 1) + K by omega, Finset.sum_range_add]
    have h2 : ∑ x ∈ range K, coeff (i + 1 + x) (frameM g zθ c b) *
        (if K + i - (i + 1 + x) < K then 0 else coeff (K + i - (i + 1 + x)) ((G *ᵥ P) b)) = 0 := by
      refine sum_eq_zero fun x hx => ?_
      have hx' : x < K := mem_range.1 hx
      simp [show K + i - (i + 1 + x) < K by omega]
    rw [h2, add_zero]
    refine sum_congr rfl fun a ha => ?_
    have ha' : a < i + 1 := mem_range.1 ha
    simp [show ¬ K + i - a < K by omega]

/-! ## The cell-digit map is bijective -/

/-- **The cells of a self-similar scramble** (the cell ring `𝔽_q[z]/(w^K)` of `sec:law`): the cell-digit
map `V ↦ (y_{c,n}(V))_{c, n<K}`, `R^{sK} → R^{s×K}`, is bijective (onto by `law_digits`; one-to-one by
counting, `R` finite). -/
theorem law_cells [Fintype R] [DecidableEq R] (g zθ : Fin s → PowerSeries R) (w : Polynomial R)
    (hw : w.natDegree ≤ s) (θ θ' : R) (hθ : θ * θ' = 1)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (hMG : frameM g zθ * G = 1) (K : ℕ) (hK : 1 ≤ K) :
    Function.Bijective (fun (V : Fin (s * K) → R) (c : Fin s) (n : Fin K) =>
      vecDigit (ssGen g zθ) V c n) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨fun T => ?_, ?_⟩
  · refine ⟨lawVec w θ' G (fun c => PowerSeries.mk fun n => if h : n < K then T c ⟨n, h⟩ else 0) K,
      funext fun c => funext fun n => ?_⟩
    show vecDigit _ _ c n = _
    rw [(law_digits g zθ w hw θ θ' hθ hroot G hMG _ K hK c).1 n n.isLt, coeff_mk]
    simp [n.isLt]
  · simp only [Fintype.card_fun, Fintype.card_fin]
    rw [← pow_mul, mul_comm K s]

/-! ## `prop:law` -/

/-- `[x^i] M Ĝ = I`: `∑_b ∑_{a ≤ i} [x^a] M[c][b] [x^{i-a}] Ĝ[b][c'] = δ_{cc'}`. -/
theorem frame_hat_one (g zθ : Fin s → PowerSeries R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (hMG : frameM g zθ * G = 1) (i : ℕ) (c c' : Fin s) :
    ∑ b, ∑ a ∈ range (i + 1), coeff a (frameM g zθ c b) * coeff (i - a) (G b c' * PowerSeries.mk 1) =
      if c = c' then 1 else 0 := by
  have e : ∀ b, ∑ a ∈ range (i + 1), coeff a (frameM g zθ c b) * coeff (i - a) (G b c' * PowerSeries.mk 1) =
      coeff i (frameM g zθ c b * (G b c' * PowerSeries.mk 1)) := by
    intro b
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a a' => coeff a (frameM g zθ c b) * coeff a' (G b c' * PowerSeries.mk 1))]
  simp only [e, ← map_sum]
  have e2 : ∑ b, frameM g zθ c b * (G b c' * PowerSeries.mk 1) =
      (frameM g zθ * G) c c' * PowerSeries.mk 1 := by
    rw [Matrix.mul_apply, sum_mul]
    simp only [mul_assoc]
  rw [e2, hMG, Matrix.one_apply]
  split_ifs <;> simp

/-- **`prop:law`** (multi-digit law, every `s`, every depth `i`): for a self-similar scramble with
local roots `w(z_c(θx)) = θx` (`eq:roots`; `deg w ≤ s`, `θ` a unit) and a right inverse `G` of the
frame matrix, at EVERY level `K ≥ l` the carry response is
`D_i(l)[c][c'] = δ_{cc'} - ∑_{a ≤ i} ∑_b [x^a] M[c][b] [x^{l+i-a}] Ĝ[b][c']` (`lawD`): the law does not
depend on `K`. -/
theorem law [Fintype R] [DecidableEq R] (g zθ : Fin s → PowerSeries R) (w : Polynomial R)
    (hw : w.natDegree ≤ s) (θ θ' : R) (hθ : θ * θ' = 1)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (hMG : frameM g zθ * G = 1)
    (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin s) :
    IsCarryEntry (ssGen g zθ) K i l c c' (lawD g zθ G i l c c') := by
  have hK : 1 ≤ K := le_trans hl hlK
  set P : Fin s → PowerSeries R := fun c'' => PowerSeries.mk fun n => carryPat K l c' c'' n with hP
  have hd := law_digits g zθ w hw θ θ' hθ hroot G hMG P K hK
  have hcell : ∀ c₁ : Fin s, ∀ n < K,
      vecDigit (ssGen g zθ) (lawVec w θ' G P K) c₁ n = carryPat K l c' c₁ n := by
    intro c₁ n hn
    rw [(hd c₁).1 n hn, hP, coeff_mk]
  refine ⟨⟨_, hcell⟩, fun V hV => ?_⟩
  have hVeq : V = lawVec w θ' G P K := by
    refine (law_cells g zθ w hw θ θ' hθ hroot G hMG K hK).1 (funext fun c₁ => funext fun n => ?_)
    simp only
    rw [hV c₁ n n.isLt, hcell c₁ n n.isLt]
  rw [hVeq, (hd c).2 i]
  have hGP : ∀ b, (G *ᵥ P) b =
      G b c' * PowerSeries.mk (fun n => if K - l ≤ n ∧ n < K then (1 : R) else 0) := by
    intro b
    show ∑ c'', G b c'' * P c'' = _
    rw [Finset.sum_eq_single c']
    · congr 1
      ext n
      simp [hP, carryPat]
    · intro c'' _ hne
      have : P c'' = 0 := by
        ext n
        simp [hP, carryPat, hne]
      rw [this, mul_zero]
    · intro h; exact absurd (mem_univ c') h
  have hPc : coeff (K + i) (P c) = 0 := by
    simp [hP, carryPat]
  have hterm : ∀ b, ∀ a ∈ range (i + 1), coeff a (frameM g zθ c b) * coeff (K + i - a) ((G *ᵥ P) b) =
      coeff a (frameM g zθ c b) * coeff (l + i - a) (G b c' * PowerSeries.mk 1) -
        coeff a (frameM g zθ c b) * coeff (i - a) (G b c' * PowerSeries.mk 1) := by
    intro b a ha
    have ha' : a < i + 1 := mem_range.1 ha
    rw [hGP, show K + i - a = K + (i - a) by omega, coeff_mul_pat _ K l (i - a) hlK,
      show l + (i - a) = l + i - a by omega, mul_sub]
  rw [hPc, Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl (hterm b)]
  simp only [Finset.sum_sub_distrib]
  rw [frame_hat_one g zθ G hMG i c c', lawD, Finset.sum_comm]
  abel

/-- **`prop:law`, first form**: `D_i(l) = [x^{l+i}] M_{>i} Ĝ`. -/
theorem law_first (g zθ : Fin s → PowerSeries R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (hMG : frameM g zθ * G = 1) (i l : ℕ) (c c' : Fin s) :
    lawD g zθ G i l c c' = coeff (l + i) ((frameTail g zθ i * G) c c' * PowerSeries.mk 1) := by
  have hsplit : ∀ b, coeff (l + i) (frameTail g zθ i c b * (G b c' * PowerSeries.mk 1)) =
      ∑ a ∈ range (l + i + 1),
          coeff a (frameM g zθ c b) * coeff (l + i - a) (G b c' * PowerSeries.mk 1) -
        ∑ a ∈ range (i + 1),
          coeff a (frameM g zθ c b) * coeff (l + i - a) (G b c' * PowerSeries.mk 1) := by
    intro b
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a a' => coeff a (frameTail g zθ i c b) * coeff a' (G b c' * PowerSeries.mk 1)),
      Nat.succ_eq_add_one]
    have split : ∀ f : ℕ → R,
        ∑ a ∈ range (l + i + 1), f a = ∑ a ∈ range (i + 1), f a + ∑ x ∈ range l, f (i + 1 + x) :=
      fun f => by rw [show l + i + 1 = (i + 1) + l by omega, Finset.sum_range_add]
    rw [split, split]
    simp only [frameTail, coeff_mk]
    have h1 : ∑ a ∈ range (i + 1), (if i < a then coeff a (frameM g zθ c b) else 0) *
        coeff (l + i - a) (G b c' * PowerSeries.mk 1) = 0 := by
      refine sum_eq_zero fun a ha => ?_
      have ha' : a < i + 1 := mem_range.1 ha
      simp [show ¬ i < a by omega]
    have h2 : ∀ x ∈ range l, (if i < i + 1 + x then coeff (i + 1 + x) (frameM g zθ c b) else 0) *
        coeff (l + i - (i + 1 + x)) (G b c' * PowerSeries.mk 1) =
        coeff (i + 1 + x) (frameM g zθ c b) *
          coeff (l + i - (i + 1 + x)) (G b c' * PowerSeries.mk 1) := by
      intro x _
      simp [show i < i + 1 + x by omega]
    rw [h1, Finset.sum_congr rfl h2]
    abel
  rw [Matrix.mul_apply, sum_mul, map_sum]
  simp only [mul_assoc, hsplit]
  rw [Finset.sum_sub_distrib, frame_hat_one g zθ G hMG (l + i) c c', lawD, Finset.sum_comm]

/-- **The frame matrix of a frame is invertible** (proof of `prop:law`: `M(0)[c][b] = g_c(0) a_c^b` is a
Vandermonde matrix with nonzero row factors): over a field, distinct places `a_c = z_c(0)` and
`g_c(0) ≠ 0` give a two-sided inverse `G` of `M`. -/
theorem frame_inv {F : Type*} [Field F] (g zθ : Fin s → PowerSeries F)
    (hplace : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0) :
    ∃ G : Matrix (Fin s) (Fin s) (PowerSeries F), frameM g zθ * G = 1 ∧ G * frameM g zθ = 1 := by
  have hdet : IsUnit (frameM g zθ).det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det]
    have e : (constantCoeff : PowerSeries F →+* F).mapMatrix (frameM g zθ) =
        Matrix.diagonal (fun c => constantCoeff (g c)) * Matrix.vandermonde (ssPlace zθ) := by
      ext c b
      simp [frameM, Matrix.diagonal_mul, Matrix.vandermonde_apply, ssPlace]
    rw [e, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde, isUnit_iff_ne_zero]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ => hg c)
      (Finset.prod_ne_zero_iff.2 fun c _ => Finset.prod_ne_zero_iff.2 fun b hb => ?_)
    exact sub_ne_zero.2 (hplace.ne (ne_of_gt (Finset.mem_Ioi.1 hb)))
  exact ⟨(frameM g zθ)⁻¹, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩

/-! ## The bridge: a `(0,sK,s)`-net has unique carry responses -/

section Bridge

variable {q : ℕ} [NeZero q]

/-- If the prefix `P_{sK}` is a `(0,sK,s)`-net, every pattern of cell digits (digits `0, …, K-1` of
every coordinate) is attained by exactly one index vector `V ∈ R^{sK}`. -/
theorem cell_existsUnique (D : DigitCode R q) (C : Gen s R) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) (T : Fin s → ℕ → R) :
    ∃! V : Fin (s * K) → R, ∀ c, ∀ n < K, vecDigit C V c n = T c n := by
  have hd : ∑ _c : Fin s, K = s * K := by simp
  set a : Fin s → ℕ := fun c => Z3Net.Proofs.digSum q K (fun n => (D.enc (T c n) : ℕ)) with hadef
  have ha : ∀ c, a c < q ^ K := fun c => Z3Net.Proofs.digSum_lt q K _ (fun _ => (D.enc _).isLt)
  have h := hnet (fun _ => K) hd a ha
  rw [existsUnique_block D (s * K) 0] at h
  refine (existsUnique_congr fun V => ?_).1 h
  refine forall_congr' fun c => ?_
  have hfun : (fun n : Fin K => (D.enc (seqDigit D C (blockIdx D (s * K) 0 V) c n) : ℕ)) =
      fun n : Fin K => (D.enc (vecDigit C V c n) : ℕ) := by
    funext n
    rw [seqDigit_block, seqDigit_zero, add_zero]
    rfl
  show Z3Net.Proofs.digSum q K _ = a c ↔ _
  rw [hfun, digSum_enc_eq_iff D K (a c) (ha c)]
  constructor
  · intro h n hn
    rw [h ⟨n, hn⟩]
    exact digOf_digSum D K (fun n => T c n) ⟨n, hn⟩
  · intro h n
    rw [h n n.isLt]
    exact (digOf_digSum D K (fun n => T c n) n).symm

/-- **Carry responses exist** for every digital sequence whose prefix `P_{sK}` is a `(0,sK,s)`-net
(the hypothesis `IsCarryEntry` of `cert`, `cert_one` can always be met). -/
theorem carry_exists (D : DigitCode R q) (C : Gen s R) (K : ℕ) (hnet : BlockNet0 D C (s * K) 0)
    (i l : ℕ) (c c' : Fin s) : ∃ d, IsCarryEntry C K i l c c' d := by
  obtain ⟨V, hV, hu⟩ := cell_existsUnique D C K hnet (fun c₁ n => carryPat K l c' c₁ n)
  exact ⟨vecDigit C V c (K + i), ⟨V, hV⟩, fun V' hV' => by rw [hu V' hV']⟩

end Bridge

/-- Carry responses are unique. -/
theorem carryEntry_unique (C : Gen s R) (K i l : ℕ) (c c' : Fin s) {d d' : R}
    (h : IsCarryEntry C K i l c c' d) (h' : IsCarryEntry C K i l c c' d') : d = d' := by
  obtain ⟨V, hV⟩ := h.1
  exact (h.2 V hV).symm.trans (h'.2 V hV)

end GeoSeq
