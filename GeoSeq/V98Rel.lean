/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Defs
public import GeoSeq.V97Corr

@[expose] public section

/-!
# GeoSeq stage V9-8 (part 1): the polynomial of a relation (`lem:reltype`)

Over any field, distinct places, any scramble of the frame.

* `frDigit_vecPoly`: `frDigit` is the digit of the generator matrices `scrGen a L` (`lem:resform`(a)).
* `relForm_eq_place`, `place_eq_locRes`: the place-`c` part of a relation is the residue
  `Res_{a_c}(V A w^{-T-1} dz)`; `relForm_eq_res`: the relation form is `[z^{-1}] (V A / w^{T+1})` (`lem:resform`(c)).
* **`relPoly_degree_lt`**: a relation of top index `T` on `P_m` has `deg A < s(T+1) - m`; **`relPoly_eq_zero_iff`**:
  `A = 0` only for the zero family (injectivity); `relPoly_eval`: `A(a_c) = f_{c,T} L_c[T][T] w_c(a_c)^{T+1}`
  (so `f_{c,T} ≠ 0 ⟺ A(a_c) ≠ 0`); **`relSpace_of_degree`**: conversely every family whose polynomial has
  `deg A < s(T+1) - m` is a relation on `P_m`; `relPoly_add`, `relPoly_smul` (linearity).
* Tools: `dvd_of_locRes` (vanishing residues against all `V` force divisibility), `wadic_unique` (uniqueness of the
  `w`-adic expansion).
-/

namespace GeoSeq

open Finset Polynomial

section Tools
variable {F : Type*} [Field F]

/-- If `Res_a(V H / ((z-a)^{K+1} U) dz) = 0` for every polynomial `V`, then `(z - a)^{K+1} ∣ H`. -/
theorem dvd_of_locRes (a : F) (K : ℕ) (H U : F[X]) (hU : U.eval a ≠ 0)
    (h : ∀ V : F[X], locRes a (K + 1) (V * H) U = 0) : (X - C a) ^ (K + 1) ∣ H := by
  rw [X_sub_C_pow_dvd_iff]
  intro j hj
  have := h ((X - C a) ^ (K - j) * U)
  have e := locRes_cancel_unit a (K + 1) (H * (X - C a) ^ (K - j)) U 1 hU
  rw [mul_one] at e
  rw [show (X - C a) ^ (K - j) * U * H = (H * (X - C a) ^ (K - j)) * U by ring, e,
    show K + 1 = (j + 1) + (K - j) by omega, locRes_cancel_pow, locRes_one] at this
  exact this

/-- `Res_a(V (z-a)^e U / ((z-a)^{k+e} U W) dz) = Res_a(V / ((z-a)^k W) dz)`. -/
lemma locRes_shift (a : F) (k e : ℕ) (V U W : F[X]) (hU : U.eval a ≠ 0) :
    locRes a (k + e) (V * ((X - C a) ^ e * U)) (U * W) = locRes a k V W := by
  rw [show V * ((X - C a) ^ e * U) = (V * (X - C a) ^ e) * U by ring, locRes_cancel_unit _ _ _ _ _ hU,
    locRes_cancel_pow]

/-- **Uniqueness of the `w`-adic expansion**: if `∑_{j<n} A_j w^j = 0` with `deg A_j < deg w`, all `A_j = 0`. -/
theorem wadic_unique (w : F[X]) (hw : w ≠ 0) :
    ∀ (n : ℕ) (A : ℕ → F[X]), (∀ j < n, (A j).degree < w.degree) →
      ∑ j ∈ range n, A j * w ^ j = 0 → ∀ j < n, A j = 0 := by
  intro n
  induction n with
  | zero => intro A _ _ j hj; omega
  | succ n ih =>
    intro A hdeg hsum
    rw [Finset.sum_range_succ'] at hsum
    have hS : ∑ j ∈ range n, A (j + 1) * w ^ (j + 1) = w * ∑ j ∈ range n, A (j + 1) * w ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hS, pow_zero, mul_one] at hsum
    have h0 : A 0 = 0 := by
      refine eq_zero_of_dvd_of_degree_lt ⟨-∑ j ∈ range n, A (j + 1) * w ^ j, ?_⟩ (hdeg 0 (by omega))
      linear_combination hsum
    rw [h0, add_zero] at hsum
    have hrest := ih (fun j => A (j + 1)) (fun j hj => hdeg (j + 1) (by omega))
      ((mul_eq_zero.mp hsum).resolve_left hw)
    intro j hj
    rcases j with _ | j
    · exact h0
    · exact hrest j (by omega)

end Tools

section Rel
variable {F : Type*} [Field F] {s : ℕ}

/-- `frDigit` is digit `n` of coordinate `c` of the generator matrices `scrGen a L`, read at the index digits
`f_0, …, f_{m-1}` (`lem:resform`(a)). -/
theorem frDigit_vecPoly (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (n : ℕ) (f : ℕ → F) (m : ℕ) :
    frDigit a L c n (vecPoly f m) = ∑ j ∈ range m, scrGen a L c n j * f j := by
  rw [scrGen_res, frDigit]
  exact Finset.sum_congr rfl fun k _ => by rw [locRes_one]

/-- Per coordinate: `∑_{n ≤ T} f_{c,n} y_{c,n}(V) = ∑_{k ≤ T} g_{c,k} [(z - a_c)^k] V`. -/
lemma place_eq (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) (V : F[X]) :
    ∑ n ∈ range (T + 1), f c n * frDigit a L c n V =
      ∑ k ∈ range (T + 1), relG L f c T k * (taylor (a c) V).coeff k := by
  have e1 : ∀ n ∈ range (T + 1), f c n * frDigit a L c n V =
      ∑ k ∈ range (T + 1), (if k ≤ n then f c n * L c n k else 0) * (taylor (a c) V).coeff k := by
    intro n hn
    have hn' : n < T + 1 := Finset.mem_range.mp hn
    rw [frDigit, Finset.mul_sum]
    rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ T + 1 by omega)]
    have hz : ∑ k ∈ Finset.Ico (n + 1) (T + 1),
        (if k ≤ n then f c n * L c n k else 0) * (taylor (a c) V).coeff k = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [if_neg (by simp at hk; omega), zero_mul]
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (by simp at hk; omega)]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [relG, Finset.sum_mul]

/-- `relG` does not depend on the top index once it is beyond the support. -/
lemma relG_ext (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (c : Fin s) (T T' k : ℕ) (hTT : T ≤ T')
    (hf : ∀ n, T < n → f c n = 0) :
    relG L f c T k = ∑ n ∈ range (T' + 1), if k ≤ n then f c n * L c n k else 0 := by
  rw [relG, ← Finset.sum_range_add_sum_Ico _ (show T + 1 ≤ T' + 1 by omega)]
  have : ∑ n ∈ Finset.Ico (T + 1) (T' + 1), (if k ≤ n then f c n * L c n k else 0) = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [hf n (by simp at hn; omega)]; simp
  rw [this, add_zero]

lemma relG_high (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (c : Fin s) (T k : ℕ) (hk : T < k) :
    relG L f c T k = 0 :=
  Finset.sum_eq_zero fun n hn => by rw [if_neg (by simp at hn; omega)]

lemma taylor_relNum_coeff (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s)
    (V : F[X]) :
    (taylor (a c) (V * relNum a L f T c)).coeff T =
      ∑ k ∈ range (T + 1), relG L f c T k * (taylor (a c) V).coeff k := by
  rw [relNum, Finset.mul_sum, map_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show V * (C (relG L f c T k) * (X - C (a c)) ^ (T - k)) =
      C (relG L f c T k) * (V * (X - C (a c)) ^ (T - k)) by ring,
    taylor_mul, taylor_C, coeff_C_mul, taylor_mul, taylor_pow, taylor_X_sub_C, coeff_mul_X_pow',
    if_pos (by omega), show T - (T - k) = k by omega]

/-- **The place-`c` part is a residue** (`lem:reltype`, proof): `∑_{k ≤ T} g_{c,k} [(z-a_c)^k] V =
Res_{a_c}(V A w^{-T-1} dz)` for every polynomial `V`. -/
theorem place_eq_locRes (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) (V : F[X]) :
    ∑ k ∈ range (T + 1), relG L f c T k * (taylor (a c) V).coeff k =
      locRes (a c) (T + 1) (V * relPoly a L f T) (wCo a c ^ (T + 1)) := by
  rw [relPoly, Finset.mul_sum, locRes_sum, ← Finset.add_sum_erase _ _ (mem_univ c)]
  have hz : ∑ c' ∈ univ.erase c, locRes (a c) (T + 1) (V * (relNum a L f T c' * wCo a c' ^ (T + 1)))
      (wCo a c ^ (T + 1)) = 0 := by
    refine Finset.sum_eq_zero fun c' hc' => ?_
    have hne : c ≠ c' := (Finset.ne_of_mem_erase hc').symm
    rw [wCo_eq a hne, mul_pow, show V * (relNum a L f T c' * ((X - C (a c)) ^ (T + 1) * wCoCo a c' c ^ (T + 1))) =
      (V * relNum a L f T c' * wCoCo a c' c ^ (T + 1)) * (X - C (a c)) ^ (T + 1) by ring]
    exact locRes_high _ _ _ _ _ le_rfl
  have e := locRes_cancel_unit (a c) (T + 1) (V * relNum a L f T c) (wCo a c ^ (T + 1)) 1
    (by rw [eval_pow]; exact pow_ne_zero _ (wCo_eval_ne a ha c))
  rw [mul_one] at e
  rw [hz, add_zero, show V * (relNum a L f T c * wCo a c ^ (T + 1)) =
      (V * relNum a L f T c) * wCo a c ^ (T + 1) by ring, e, locRes_one, taylor_relNum_coeff]

/-- The relation form as a sum of residues of `V A / w^{T+1}`. -/
theorem relForm_eq_res (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T : ℕ) (V : F[X]) :
    relForm a L T f V = ∑ c, resAt a (fun _ => T + 1) (V * relPoly a L f T) c := by
  rw [relForm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [place_eq, place_eq_locRes a ha, resAt, placeCo_const]

lemma natDegree_relNum (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) :
    (relNum a L f T c).natDegree ≤ T := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]; omega

lemma natDegree_relPoly (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) :
    (relPoly a L f T).natDegree ≤ s * (T + 1) - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
  refine natDegree_mul_le.trans ?_
  have h1 := natDegree_relNum a L f T c
  have h2 : (wCo a c ^ (T + 1)).natDegree ≤ (s - 1) * (T + 1) := by
    rw [natDegree_pow, natDegree_wCo, mul_comm]
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact c.elim0)
  have : T + (s - 1) * (T + 1) = s * (T + 1) - 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring_nf; omega
  omega

/-- **`lem:reltype`, degree bound**: for a relation of top index `T` on `P_m`, `deg A < s(T+1) - m`. -/
theorem relPoly_degree_lt (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T m : ℕ) (hf : f ∈ relSpace a L T m) :
    (relPoly a L f T).degree < ((s * (T + 1) - m : ℕ) : WithBot ℕ) := by
  set A := relPoly a L f T
  set M := s * (T + 1)
  have hA : A.natDegree ≤ M - 1 := natDegree_relPoly a L f T
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    have : A = 0 := by simp [A, relPoly]
    rw [this, degree_zero]; exact WithBot.bot_lt_coe _
  have hM1 : 1 ≤ M := by simp only [M]; nlinarith
  have hs : (∑ c : Fin s, (fun _ => T + 1) c) = M := by simp [M, Finset.sum_const]
  -- coefficient `M - 1 - d` vanishes for `d < min m M` (strong induction on `d`)
  have key : ∀ d, d < m → d < M → A.coeff (M - 1 - d) = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hdm hdM
      have hdeg : (X ^ d * A).natDegree ≤ M - 1 := by
        rcases eq_or_ne A 0 with h0 | h0
        · rw [h0, mul_zero, natDegree_zero]; exact Nat.zero_le _
        · rw [natDegree_mul (pow_ne_zero _ X_ne_zero) h0, natDegree_X_pow]
          have : A.natDegree ≤ M - 1 - d := by
            refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
            have hj' : M - 1 - d < j := by exact_mod_cast hj
            rcases Nat.lt_or_ge (M - 1) j with h1 | h1
            · exact coeff_eq_zero_of_natDegree_lt (by omega)
            · have := ih (M - 1 - j) (by omega) (by omega) (by omega)
              rwa [show M - 1 - (M - 1 - j) = j by omega] at this
          omega
      have h := hf.2 (X ^ d) (by rw [natDegree_X_pow]; omega)
      rw [relForm_eq_res a ha, res_thm_of_deg a ha _ _ (by rw [hs]; exact lt_of_le_of_lt hdeg (by omega)),
        hs, coeff_X_pow_mul',
        if_pos (by omega)] at h
      exact h
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  have hj' : s * (T + 1) - m ≤ j := by exact_mod_cast hj
  rcases Nat.lt_or_ge (M - 1) j with h1 | h1
  · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · have := key (M - 1 - j) (by omega) (by omega)
    rwa [show M - 1 - (M - 1 - j) = j by omega] at this

lemma wPoly_eq_placePoly (a : Fin s → F) : wPoly a = placePoly a (fun _ => 1) := by
  simp [wPoly, placePoly]

lemma wPoly_monic (a : Fin s → F) : (wPoly a).Monic := by
  rw [wPoly_eq_placePoly]; exact placePoly_monic a _

lemma natDegree_wPoly (a : Fin s → F) : (wPoly a).natDegree = s := by
  rw [wPoly_eq_placePoly, placePoly_natDegree]; simp

lemma taylor_X_sub_C_pow_coeff (b : F) (k j : ℕ) :
    (taylor b ((X - C b) ^ k)).coeff j = if j = k then 1 else 0 := by
  rw [taylor_pow, taylor_X_sub_C, coeff_X_pow]

/-- If `A = 0`, every place part vanishes: `g_{c,k} = 0` for `k ≤ T`. -/
theorem relG_zero_of_relPoly (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T : ℕ) (hA : relPoly a L f T = 0) (c : Fin s) (k : ℕ) (hk : k ≤ T) :
    relG L f c T k = 0 := by
  have h := place_eq_locRes a ha L f T c ((X - C (a c)) ^ k)
  rw [hA, mul_zero, locRes_zero_num] at h
  rw [← h, Finset.sum_eq_single k]
  · rw [taylor_X_sub_C_pow_coeff, if_pos rfl, mul_one]
  · intro j _ hj; rw [taylor_X_sub_C_pow_coeff, if_neg hj, mul_zero]
  · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'

/-- The triangular system `g_{c,k} = ∑_{k ≤ n ≤ T} f_{c,n} L_c[n][k]` (`k ≤ T`) has only the zero solution. -/
theorem eq_zero_of_relG (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s)
    (hf : ∀ n, T < n → f c n = 0) (h : ∀ k ≤ T, relG L f c T k = 0) : ∀ n, f c n = 0 := by
  have key : ∀ e n, n + e = T → f c n = 0 := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro n hn
      have hg := h n (by omega)
      rw [relG, Finset.sum_eq_single n] at hg
      · rw [if_pos le_rfl] at hg
        exact (mul_eq_zero.mp hg).resolve_right (hL c n)
      · intro n' hn' hne
        split_ifs with hle
        · rw [ih (T - n') (by simp at hn'; omega) n' (by simp at hn'; omega), zero_mul]
        · rfl
      · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'
  intro n
  rcases Nat.lt_or_ge T n with h1 | h1
  · exact hf n h1
  · exact key (T - n) n (by omega)

/-- **`lem:reltype`, injectivity**: the polynomial of a family of top index `T` vanishes only for the zero family. -/
theorem relPoly_eq_zero_iff (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (hL : IsScramble L) (f : Fin s → ℕ → F) (T : ℕ) (hf : ∀ c n, T < n → f c n = 0) :
    relPoly a L f T = 0 ↔ f = 0 := by
  constructor
  · intro hA
    funext c n
    exact eq_zero_of_relG L hL f T c (hf c) (fun k hk => relG_zero_of_relPoly a ha L f T hA c k hk) n
  · rintro rfl
    simp [relPoly, relNum, relG]

/-- **`lem:reltype`, the leading digits**: `A(a_c) = f_{c,T} L_c[T][T] w_c(a_c)^{T+1}`; so `f_{c,T} ≠ 0` exactly when
`A(a_c) ≠ 0` (`relPoly_eval_ne_iff`). -/
theorem relPoly_eval (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) :
    (relPoly a L f T).eval (a c) = f c T * L c T T * (wCo a c).eval (a c) ^ (T + 1) := by
  rw [relPoly, eval_finset_sum, Finset.sum_eq_single c]
  · rw [eval_mul, eval_pow, relNum, eval_finset_sum, Finset.sum_eq_single T]
    · rw [eval_mul, eval_C, Nat.sub_self, pow_zero, eval_one, mul_one, relG, Finset.sum_eq_single T]
      · rw [if_pos le_rfl]
      · intro n hn hne; rw [if_neg (by simp at hn; omega)]
      · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'
    · intro k hk hne
      rw [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_self,
        zero_pow (by simp at hk; omega), mul_zero]
    · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'
  · intro c' _ hne
    rw [eval_mul, eval_pow, wCo_eval_other a (Ne.symm hne), zero_pow (by omega), mul_zero]
  · intro h'; exact absurd (mem_univ c) h'

theorem relPoly_eval_ne_iff (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (hL : IsScramble L) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) :
    (relPoly a L f T).eval (a c) ≠ 0 ↔ f c T ≠ 0 := by
  rw [relPoly_eval]
  constructor
  · intro h h0; rw [h0, zero_mul, zero_mul] at h; exact h rfl
  · intro h
    exact mul_ne_zero (mul_ne_zero h (hL c T)) (pow_ne_zero _ (wCo_eval_ne a ha c))

/-- **`lem:reltype`, converse**: a family of top index `T` whose polynomial has `deg A < s(T+1) - m` is a relation
on `P_m`. -/
theorem relSpace_of_degree (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (f : Fin s → ℕ → F) (T m : ℕ) (hf : ∀ c n, T < n → f c n = 0)
    (hdeg : (relPoly a L f T).degree < ((s * (T + 1) - m : ℕ) : WithBot ℕ)) :
    f ∈ relSpace a L T m := by
  refine ⟨hf, fun V hV => ?_⟩
  rw [relForm_eq_res a ha]
  rcases eq_or_ne (relPoly a L f T) 0 with h0 | h0
  · rw [h0, mul_zero]; simp [resAt, locRes_zero_num]
  · have hA : (relPoly a L f T).natDegree < s * (T + 1) - m := by
      rw [degree_eq_natDegree h0] at hdeg; exact_mod_cast hdeg
    refine res_thm_zero a ha _ _ ?_
    have hs : (∑ c : Fin s, (fun _ => T + 1) c) = s * (T + 1) := by simp [Finset.sum_const]
    rw [hs]
    have := natDegree_mul_le (p := V) (q := relPoly a L f T)
    omega

lemma relG_add (L : Fin s → ℕ → ℕ → F) (f g : Fin s → ℕ → F) (c : Fin s) (T k : ℕ) :
    relG L (f + g) c T k = relG L f c T k + relG L g c T k := by
  rw [relG, relG, relG, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by simp only [Pi.add_apply]; split_ifs <;> ring

lemma relG_smul (L : Fin s → ℕ → ℕ → F) (r : F) (f : Fin s → ℕ → F) (c : Fin s) (T k : ℕ) :
    relG L (r • f) c T k = r * relG L f c T k := by
  rw [relG, relG, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `lem:reltype`: the polynomial is linear in the relation. -/
theorem relPoly_add (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f g : Fin s → ℕ → F) (T : ℕ) :
    relPoly a L (f + g) T = relPoly a L f T + relPoly a L g T := by
  simp only [relPoly, relNum, relG_add, C_add, add_mul, Finset.sum_add_distrib]

theorem relPoly_smul (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (r : F) (f : Fin s → ℕ → F) (T : ℕ) :
    relPoly a L (r • f) T = C r * relPoly a L f T := by
  simp only [relPoly, relNum, relG_smul, C_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

end Rel

end GeoSeq
