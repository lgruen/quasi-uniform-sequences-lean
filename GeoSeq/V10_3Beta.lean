/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_3Defs
public import GeoSeq.V94Thm
public import GeoSeq.Prefix
public import GeoSeq.V9QU
public import GeoSeq.Cert

@[expose] public section

/-!
# GeoSeq stage V10-3: `prop:primepower`, the soundness of the certificate (proved once)

* `mem_vecsOf`, `ppCheck_spec`: what `ppCheck = true` says.
* `gapNum_one_ge`: `q f_1(e, σ) ≥ N` from `N + 1 ≤ |e q + enc(r + σ) - enc r|` for every digit `r` (any digit code).
* `resStar_carryChange`: the carry change of the staggered coordinate of `𝓡^⋆_v` over any field and any digit code:
  a step of coordinate `c ≠ c⋆` with carry length `l`, stopping at the digit `y`, changes `r_{c⋆}` by `Δ k_c`,
  `Δ = Δ(y)` for `l = 1` and `Δ = Δ(ȳ)` for `l ≥ 2` (the proof of `prop:primepower`, via `eq:carrychange`).
* **`pp_sep`**: for EVERY finite field `F`, EVERY digit code `D` (`q ≥ 4`), distinct places, `θ, μ⋆ ≠ 0`, nonzero
  weights `w`, any list `Δs` containing every digit increment `Δ(y)` and any `N` certified by `ppCheck`:
  `sep(P_{sK}) ≥ N/q` for every `K ≥ 1`. **`primepower_of_check`**: the whole conclusion `PPConcl` (`N ≥ 1`).
  The natural identification is not used: only the set of digit increments enters.
-/

namespace GeoSeq

open Finset

/-- Every vector with entries in `L` is listed by `vecsOf`. -/
theorem mem_vecsOf {α : Type*} (L : List α) (n : ℕ) (v : Fin n → α) (h : ∀ i, v i ∈ L) : v ∈ vecsOf n L := by
  induction n with
  | zero =>
    simp only [vecsOf, List.mem_singleton]
    funext i; exact i.elim0
  | succ n ih =>
    simp only [vecsOf]
    exact List.mem_flatMap.mpr ⟨v 0, h 0, List.mem_map.mpr ⟨Fin.tail v, ih _ fun i => h _, Fin.cons_self_tail v⟩⟩

/-- Every vector with entry `i` in `L i` is listed by `vecsOfL`. -/
theorem mem_vecsOfL {α : Type*} (n : ℕ) (L : Fin n → List α) (v : Fin n → α) (h : ∀ i, v i ∈ L i) :
    v ∈ vecsOfL n L := by
  induction n with
  | zero =>
    simp only [vecsOfL, List.mem_singleton]
    funext i; exact i.elim0
  | succ n ih =>
    simp only [vecsOfL]
    exact List.mem_flatMap.mpr ⟨v 0, h 0, List.mem_map.mpr ⟨Fin.tail v, ih _ _ fun i => h _, Fin.cons_self_tail v⟩⟩

/-- `smul3 e x = e x` for `e ∈ {-1, 0, 1}`. -/
theorem smul3_eq {F : Type*} [Ring F] (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (x : F) : smul3 e x = ((e : ℤ) : F) * x := by
  have : e = -1 ∨ e = 0 ∨ e = 1 := by omega
  rcases this with rfl | rfl | rfl <;> simp [smul3]

/-- What the certificate says, one step at a time. -/
theorem ppCheck_spec {F : Type*} [CommRing F] [DecidableEq F] {enc : F → ℕ} {q : ℕ} {elems Δs : List F} {n : ℕ}
    {w : Fin n → F} {prods : Fin n → List F} {S : List F} {N : ℕ}
    (hchk : ppCheck enc q elems Δs n w prods S N = true) (es : ℤ) (hes : -1 ≤ es ∧ es ≤ 1)
    (e' : Fin n → ℤ) (he' : ∀ i, -1 ≤ e' i ∧ e' i ≤ 1) (Δ : Fin n → F) (hΔ : ∀ i, Δ i ∈ Δs)
    (hnz : ¬ (es = 0 ∧ ∀ i, e' i = 0)) (r : F) (hr : r ∈ elems) :
    N + 1 ≤ ((es * q + (enc (r + ∑ i, ((e' i : ℤ) : F) * w i * Δ i) : ℤ) - enc r).natAbs) := by
  have hmem : ∀ x : ℤ, -1 ≤ x ∧ x ≤ 1 → x ∈ [(-1 : ℤ), 0, 1] := by
    intro x hx
    have : x = -1 ∨ x = 0 ∨ x = 1 := by omega
    rcases this with h | h | h <;> simp [h]
  unfold ppCheck at hchk
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at hchk
  obtain ⟨⟨⟨hNq, hprod⟩, hsig⟩, hS⟩ := hchk
  by_cases h0 : ∀ i, e' i = 0
  · have hes0 : es ≠ 0 := fun h => hnz ⟨h, h0⟩
    have hz : ∑ i, ((e' i : ℤ) : F) * w i * Δ i = 0 := Finset.sum_eq_zero fun i _ => by rw [h0 i]; simp
    rw [hz, add_zero, add_sub_cancel_right]
    have : es = 1 ∨ es = -1 := by omega
    rcases this with rfl | rfl <;> simp <;> omega
  · have hP : (fun i => w i * Δ i) ∈ vecsOfL n prods :=
      mem_vecsOfL n prods _ fun i => hprod i (List.mem_finRange i) (Δ i) (hΔ i)
    have h1 := hsig e' (mem_vecsOf _ n e' fun i => hmem _ (he' i))
    simp only [Bool.or_eq_true, decide_eq_true_iff, List.all_eq_true] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 h0
    have hσ : ∑ i, smul3 (e' i) (w i * Δ i) = ∑ i, ((e' i : ℤ) : F) * w i * Δ i :=
      Finset.sum_congr rfl fun i _ => by rw [smul3_eq _ (he' i), mul_assoc]
    have h2 := h1 _ hP
    rw [hσ] at h2
    have h3 := hS _ h2 es (hmem es hes)
    unfold gapOK at h3
    rw [List.all_eq_true] at h3
    exact of_decide_eq_true (h3 r hr)

/-- `q f_1(e, σ) ≥ N` (`gapNum` with one digit, any digit code) from the bound at every digit. -/
theorem gapNum_one_ge {F : Type*} [CommRing F] [Fintype F] [DecidableEq F] {q : ℕ} (D : DigitCode F q)
    (e : ℤ) (σ : Fin 1 → F) (N : ℕ)
    (h : ∀ r : F, N + 1 ≤ ((e * q + ((D.enc (r + σ 0) : ℕ) : ℤ) - ((D.enc r : ℕ) : ℤ)).natAbs)) :
    N ≤ gapNum D 1 e σ := by
  unfold gapNum
  set S := univ.image fun r : Fin 1 → F =>
    ((e * (q : ℤ) ^ 1 + (encVec D (r + σ) : ℤ) - (encVec D r : ℤ)).natAbs) with hS
  have hne : S.Nonempty := by simp [hS]
  obtain ⟨r0, -, hr0⟩ := mem_image.mp (S.min'_mem hne)
  have hev : ∀ r : Fin 1 → F, encVec D r = (D.enc (r 0) : ℕ) := by
    intro r; simp [encVec]
  have := h (r0 0)
  rw [← hr0, hev, hev, pow_one, Pi.add_apply]
  omega

section Star
variable {F : Type*} [Field F] {s : ℕ}

/-- The carry change of the staggered coordinate (proof of `prop:primepower`): with the one-digit responses
`D(0) = 0` and `D(l)[c⋆][c'] = k'_{c'}` (`l ≥ 1`), `δ_0(l, y)[c⋆][c'] = Δ k'_{c'}` with `Δ = Δ(y)` for `l = 1`
and `Δ = Δ(ȳ)` for `l ≥ 2` (`eq:carrychange`). -/
theorem carryChange_const {q : ℕ} [NeZero q] (D : DigitCode F q) (Dr : ℕ → ℕ → Fin s → Fin s → F)
    (cs c' : Fin s) (kc : F) (hDr : ∀ l, Dr 0 l cs c' = if l = 0 then 0 else kc) (l : ℕ) (hl : 1 ≤ l) (y : F) :
    carryChange D Dr 0 l y cs c' = (if l = 1 then digInc D y else digInc D (topDigit D)) * kc := by
  unfold carryChange
  rw [hDr, hDr]
  by_cases h1 : l = 1
  · subst h1; simp
  · rw [if_neg (show l - 1 ≠ 0 by omega), if_neg (show l ≠ 0 by omega), if_neg h1]; ring

end Star

section Main
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-- **`prop:primepower`, separation** (soundness of the certificate, every finite field and every digit code). Let
`s = n + 1`, `q ≥ 4`, the places distinct, `θ, μ⋆ ≠ 0`, the weights `k_{c⋆.succAbove i} = w_i ≠ 0`, `elems` a list of
all digits, `Δs` a list containing every digit increment `Δ(y)` (`rem:F4carry`), and `ppCheck … N = true`. Then
`sep(P_{sK}) ≥ N/q` for every `K ≥ 1`. -/
theorem pp_sep (D : DigitCode F q) (hq : 4 ≤ q) {n : ℕ} (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (θ : F) (hθ : θ ≠ 0) (cs : Fin (n + 1)) (μs : F) (hμ : μs ≠ 0) (k : Fin (n + 1) → F) (w : Fin n → F)
    (hw : ∀ i, w i ≠ 0) (hk : ∀ i, k (cs.succAbove i) = w i) (elems Δs : List F) (hel : ∀ y, y ∈ elems)
    (hΔ : ∀ y, digInc D y ∈ Δs) (prods : Fin n → List F) (S : List F) (N : ℕ)
    (hchk : ppCheck (fun y => (D.enc y : ℕ)) q elems Δs n w prods S N = true)
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel q (n + 1) K (seqPoint D (resStar a θ cs μs k)) ((N : ℝ) / q) := by
  classical
  set C := resStar a θ cs μs k with hC
  have hkne : ∀ c, c ≠ cs → k c ≠ 0 := by
    intro c hc
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hc
    rw [hk]; exact hw i
  have hnet : BlockNet0 D C ((n + 1) * K) 0 := resStar_t0 D a ha θ hθ cs μs hμ k hkne ((n + 1) * K) 0
  have hqK : 4 ≤ q ^ K := le_trans hq (Nat.le_self_pow (by omega) q)
  set k' : Fin (n + 1) → F := fun c' => if c' = cs then 0 else k c' with hk'
  let Dr : ℕ → ℕ → Fin (n + 1) → Fin (n + 1) → F := fun i l c c' =>
    if l = 0 then 0 else if c = cs then k' c' else
      if h : 1 ≤ l ∧ l ≤ K then Classical.choose (carry_exists D C K hnet i l c c') else 0
  have hD0 : ∀ i c c', Dr i 0 c c' = 0 := fun i c c' => by simp [Dr]
  have hD : ∀ i < 1, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c') := by
    intro i hi l hl hlK c c'
    obtain rfl : i = 0 := by omega
    by_cases hc : c = cs
    · subst hc
      have := resStar_carry D a ha θ c μs k hkne K hK hnet l hl hlK c'
      simpa [Dr, show l ≠ 0 by omega, hk'] using this
    · simp only [Dr, if_neg (show l ≠ 0 by omega), if_neg hc, And.intro hl hlK, and_self, dite_true]
      exact Classical.choose_spec (carry_exists D C K hnet 0 l c c')
  have hDrow : ∀ c' l, Dr 0 l cs c' = if l = 0 then 0 else k' c' := by
    intro c' l; by_cases hl : l = 0 <;> simp [Dr, hl]
  -- the elements of the lists
  have hmem01 : ∀ x : ℤ, -1 ≤ x ∧ x ≤ 1 → -1 ≤ x ∧ x ≤ 1 := fun x h => h
  -- `N ≤ q - 1` from the axis step of `c⋆`
  have hNq : (N : ℝ) / q ≤ 1 := by
    have h := ppCheck_spec hchk 1 (by norm_num) (fun _ => 0) (fun _ => by norm_num)
      (fun _ => digInc D 0) (fun _ => hΔ 0) (by simp) 0 (hel 0)
    simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero, one_mul] at h
    have h2 : N + 1 ≤ q := by
      have : ((q : ℤ) + ((D.enc (0 : F) : ℕ) : ℤ) - ((D.enc (0 : F) : ℕ) : ℤ)).natAbs = q := by
        rw [add_sub_cancel_right]; exact Int.natAbs_natCast q
      omega
    rw [div_le_one (by exact_mod_cast (show 0 < q by omega))]
    exact_mod_cast (show N ≤ q by omega)
  have h := cert D C K 1 hqK hnet Dr hD0 hD ((N : ℝ) / q) ?_
  · rwa [min_eq_right hNq] at h
  intro e l hst y
  obtain ⟨he, hne, hl⟩ := hst
  -- the term of `c⋆`
  set Δv : Fin (n + 1) → F := fun c' => if l c' = 1 then digInc D (y c') else digInc D (topDigit D) with hΔv
  have hσ : certSigma D Dr 1 e l y cs 0 = ∑ i, ((e (cs.succAbove i) : ℤ) : F) * w i * Δv (cs.succAbove i) := by
    show ∑ c', ((e c' : ℤ) : F) * carryChange D Dr 0 (l c') (y c') cs c' = _
    rw [Fin.sum_univ_succAbove _ cs]
    have h1 : ∀ c', carryChange D Dr 0 (l c') (y c') cs c' = Δv c' * k' c' := fun c' =>
      carryChange_const D Dr cs c' (k' c') (hDrow c') (l c') (hl c').1 (y c')
    simp only [h1, hk', if_pos rfl, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_neg (Fin.succAbove_ne cs i), hk]; ring
  have hgap : N ≤ gapNum D 1 (e cs) (certSigma D Dr 1 e l y cs) := by
    refine gapNum_one_ge D _ _ N fun r => ?_
    rw [hσ]
    refine ppCheck_spec hchk (e cs) (he cs) (fun i => e (cs.succAbove i)) (fun i => he _) (fun i => Δv (cs.succAbove i))
      (fun i => ?_) ?_ r (hel r)
    · simp only [hΔv]; split_ifs <;> exact hΔ _
    · rintro ⟨h0, h1⟩
      obtain ⟨c, hc⟩ := hne
      by_cases hcs : c = cs
      · exact hc (hcs ▸ h0)
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hcs
        exact hc (h1 i)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  unfold certTerm
  calc (N : ℝ) / q ≤ (gapNum D 1 (e cs) (certSigma D Dr 1 e l y cs) : ℝ) / (q : ℝ) ^ 1 := by
        rw [pow_one]; exact div_le_div_of_nonneg_right (by exact_mod_cast hgap) hq0.le
    _ = Real.sqrt (((gapNum D 1 (e cs) (certSigma D Dr 1 e l y cs) : ℝ) / (q : ℝ) ^ 1) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
        (f := fun c => ((gapNum D 1 (e c) (certSigma D Dr 1 e l y c) : ℝ) / (q : ℝ) ^ 1) ^ 2)
        (fun c _ => sq_nonneg _) (mem_univ cs))

/-- **`prop:primepower`** (soundness, the whole conclusion): with the hypotheses of `pp_sep` and `N ≥ 1`, the staggered
residue sequence over `F` is a digital `(0,s)`-sequence with `sep(P_{sK}) ≥ N/q` for every `K ≥ 1`,
`δ(P_{[N']}) ≥ (N/q²) N'^{-1/s}` for every `N' ≥ 2`, and quasi-uniform. -/
theorem primepower_of_check (D : DigitCode F q) (hq : 4 ≤ q) {n : ℕ} (a : Fin (n + 1) → F)
    (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (cs : Fin (n + 1)) (μs : F) (hμ : μs ≠ 0)
    (k : Fin (n + 1) → F) (w : Fin n → F) (hw : ∀ i, w i ≠ 0) (hk : ∀ i, k (cs.succAbove i) = w i)
    (elems Δs : List F) (hel : ∀ y, y ∈ elems) (hΔ : ∀ y, digInc D y ∈ Δs) (prods : Fin n → List F) (S : List F) (N : ℕ)
    (hN : 1 ≤ N) (hchk : ppCheck (fun y => (D.enc y : ℕ)) q elems Δs n w prods S N = true) :
    PPConcl D (n + 1) (resStar a θ cs μs k) ((N : ℝ) / q) := by
  have hkne : ∀ c, c ≠ cs → k c ≠ 0 := by
    intro c hc
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hc
    rw [hk]; exact hw i
  have hseq := resStar_t0 D a ha θ hθ cs μs hμ k hkne
  have hsep := fun K hK => pp_sep D hq a ha θ hθ cs μs hμ k w hw hk elems Δs hel hΔ prods S N hchk K hK
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hβ : (0 : ℝ) < (N : ℝ) / q := div_pos (by exact_mod_cast hN) hq0
  have hall := prefix_sep q (n + 1) (by omega) (by omega) _ _ hβ.le hsep
  exact ⟨hseq, hsep, hall, qu_of_sepAllN D _ (by omega) (by omega) hseq _ (div_pos hβ hq0) hall⟩

end Main

end GeoSeq
