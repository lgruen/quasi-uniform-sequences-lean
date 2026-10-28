/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V93Thm
public import GeoSeq.V9Res
public import GeoSeq.V9Kor

@[expose] public section

/-!
# GeoSeq stage V9-3 (part 4): Halton-type and Faure sequences (`cor:halton`, `cor:faure`)

* `haltonY_lin`, `haltonY_radInv` (`sec:polybases`): the coordinates of the Halton-type sequence of
  Goda–Hofer–Suzuki (Def. 2) are linear `b_c`-adic radical inverses with digit map
  `π(a) = ([z^{e-1}] a, …, [z^0] a)`.
* `haltonPt_eq_linPt`: the finite-sum definition `haltonPt` (the Palomar statement's) is the point of the
  linear-coordinate sequence `haltonY` (`linPt`, an infinite digit expansion whose digits vanish beyond
  `(n+1) e_c`).
* **`halton_not_quasiUniform`** (**`cor:halton`**, GHS Open Problem 2): for every prime `p`, `s ≥ 2` and pairwise
  coprime `b_c ∈ 𝔽_p[z]` of degrees `≥ 1` (not necessarily monic or irreducible), the Halton-type sequence has
  prefixes `P_m` with two points at distance `< ε p^{-m/s}` for every `ε > 0`, and is not quasi-uniform. The
  statement is the theorem of `HeadlineSeqV4/Challenge_combined_explicit.lean` with the library's names.
* `halton_pair` (`cor:halton`, explicit pairs): `g = Σ = 1 + z + ⋯ + z^{e-1}`, `g̃ = -Σ'`, `g' = -Σ`.
* `taylor_coeff_eq_badicDigit`: the Taylor digits at `a` are the `(z - a)`-adic digits.
* **`faure_not_quasiUniform`** (**`cor:faure`**, prime `q = p`): the unscrambled frame `(P_{a_0}, …, P_{a_{s-1}})`
  with distinct places is not quasi-uniform; `faureSeq_not_quasiUniform`: the Faure sequence
  `(P^0, …, P^{s-1})`, `2 ≤ s ≤ p`.
-/

namespace GeoSeq

open Finset Polynomial

section HaltonCoords
variable {F : Type*} [Field F] {s : ℕ}

theorem haltonY_lin (b : Fin s → F[X]) (c : Fin s) : IsLinCoord (haltonY b c) := by
  intro V W n
  simp only [haltonY, haltonPi, badicDigit_add, coeff_add]

lemma coeff_sum_X_pow (n k : ℕ) : (∑ j ∈ range n, (X : F[X]) ^ j).coeff k = if k < n then 1 else 0 := by
  rw [finsetSum_coeff]
  simp_rw [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma natDegree_sum_X_pow (n : ℕ) : (∑ j ∈ range n, (X : F[X]) ^ j).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun j hj => by
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega

theorem haltonY_radInv (b : Fin s → F[X]) (c : Fin s) (hb : 1 ≤ (b c).natDegree) :
    IsRadInv (haltonY b c) (b c) (haltonPi (b c).natDegree) := by
  set e := (b c).natDegree with he
  refine ⟨fun u => ⟨∑ i ∈ range e, C (u i) * X ^ (e - 1 - i), ?_, fun i hi => ?_⟩, fun V Q i hi => ?_⟩
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_) (by omega : e - 1 < e)
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · rw [haltonPi, finsetSum_coeff, Finset.sum_eq_single i]
    · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
    · intro j hj hji
      rw [coeff_C_mul_X_pow, ite_eq_right]
      have := Finset.mem_range.mp hj; omega
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · have hQ : (Q * e + i) / e = Q := by
      rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, zero_add]
    have hi' : (Q * e + i) % e = i := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [haltonY, ← he, hQ, hi']

end HaltonCoords

/-! ## The Halton-type sequence as a linear-coordinate sequence -/

section Halton
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

lemma sum_range_mul_eq (f : ℕ → ℝ) (e : ℕ) :
    ∀ N, ∑ j ∈ range (N * e), f j = ∑ Q ∈ range N, ∑ i ∈ range e, f (Q * e + i)
  | 0 => by simp
  | N + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul_eq f e N, Finset.sum_range_succ]

/-- The Palomar statement's finite-sum `haltonPt` is the point of the linear-coordinate sequence `haltonY`. -/
theorem haltonPt_eq_linPt (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) :
    haltonPt p b = linPt p (haltonY b) := by
  funext n c
  set e := (b c).natDegree with he
  have he1 : 1 ≤ e := hdeg c
  unfold linPt
  rw [tsum_eq_sum (s := range ((n + 1) * e)), sum_range_mul_eq _ e (n + 1)]
  · unfold haltonPt
    refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hQ : (Q * e + i) / e = Q := by
      rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi', zero_add]
    have hr : (Q * e + i) % e = i := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
    simp only [haltonY, haltonPi, ← he, hQ, hr]
  · intro j hj
    have hj' : (n + 1) * e ≤ j := by simpa using hj
    have hQ : n + 1 ≤ j / e := (Nat.le_div_iff_mul_le (by omega)).mpr hj'
    have hdg : (idxPolyP p n).natDegree < e * (j / e) := by
      have := natDegree_idxPolyP (p := p) n
      have : n + 1 ≤ e * (j / e) := hQ.trans (Nat.le_mul_of_pos_left _ (by omega))
      omega
    simp only [haltonY, haltonPi, ← he, badicDigit_high he1 hdg, coeff_zero, ZMod.val_zero,
      Nat.cast_zero, zero_div]

end Halton

/-- **`cor:halton`** (Goda–Hofer–Suzuki, Open Problem 2). For every prime `p`, every `s ≥ 2` and all pairwise
coprime `b_0, …, b_{s-1} ∈ 𝔽_p[z]` of degrees `≥ 1` (not necessarily monic or irreducible), the Halton-type
sequence in these bases has, for every `ε > 0`, a prefix of `p^m` points containing two points at Euclidean
distance `< ε p^{-m/s}`; and it is not quasi-uniform. -/
theorem halton_not_quasiUniform (p : ℕ) [Fact p.Prime] (s : ℕ) (hs : 2 ≤ s)
    (b : Fin s → Polynomial (ZMod p)) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (haltonPt p b v) (haltonPt p b w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (haltonPt p b) := by
  rw [haltonPt_eq_linPt b hdeg]
  have ch : Fin s := ⟨0, by omega⟩
  exact nonqu hs (haltonY b) (fun c => haltonY_lin b c) b hdeg hcop ch
    (fun c _ => (haltonY_radInv b c (hdeg c)).isBAdic (hdeg c) (haltonY_lin b c))
    (haltonPi (b ch).natDegree) (haltonY_radInv b ch (hdeg ch))

/-- **`cor:halton`**, the explicit pairs. For any coordinate `ĉ` (`b = b_ĉ`, `e = deg b`), with
`Σ = 1 + z + ⋯ + z^{e-1}`, `Σ' = 1 + z + ⋯ + z^{e-2}`, admissible `ν, k, η` of `thm:nonqu` and `Q = p^w`: the indices
`ι(V_1)`, `ι(V_2)`, `V_1 = -Σ' b^{Qη} - Σ b^{Qη+1} S_{Qν-1}`, `V_2 = V_1 + Σ b^{Qη} S_{Qν} Θ^{Qk}`, are distinct and
`< p^{m_Q}`, and the two points of the Halton-type sequence are at distance `< √(s+3) p^{-L_Q}`. -/
theorem halton_pair (p : ℕ) [Fact p.Prime] (s : ℕ) (hs : 2 ≤ s)
    (b : Fin s → Polynomial (ZMod p)) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    let Sg : Polynomial (ZMod p) := ∑ j ∈ range (b ch).natDegree, X ^ j
    let Sg' : Polynomial (ZMod p) := ∑ j ∈ range ((b ch).natDegree - 1), X ^ j
    polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w) + nonquD b ch Sg ν k η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w)) ≠
        polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w) + nonquD b ch Sg ν k η (p ^ w)) ∧
      euclDist (haltonPt p b (polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w))))
        (haltonPt p b (polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w) + nonquD b ch Sg ν k η (p ^ w)))) <
        Real.sqrt (s + 3) / (p : ℝ) ^ (p ^ w * lcmDeg b * (k + 1)) := by
  intro Sg Sg'
  set e := (b ch).natDegree with he
  have he1 : 1 ≤ e := hdeg ch
  rw [haltonPt_eq_linPt b hdeg]
  have hSg : Sg.natDegree < e := lt_of_le_of_lt (natDegree_sum_X_pow _) (by omega)
  have hSg' : Sg'.natDegree < e := lt_of_le_of_lt (natDegree_sum_X_pow _) (by omega)
  refine nonqu_pair hs (haltonY b) (fun c => haltonY_lin b c) b hdeg ch
    (fun c _ => (haltonY_radInv b c (hdeg c)).isBAdic (hdeg c) (haltonY_lin b c))
    (haltonPi e) (haltonY_radInv b ch he1) Sg (-Sg') (-Sg) hSg (by rwa [natDegree_neg])
    (by rwa [natDegree_neg]) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) ν k η hν hR hΘ hη w
  · simp only [haltonPi, Sg, coeff_sum_X_pow, ← he]; rw [ite_eq_left (by omega)]
  · simp only [haltonPi, Sg', coeff_neg, coeff_sum_X_pow, ← he]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [ite_eq_right (by omega), ite_eq_left h0]; exact neg_zero
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]; rfl
  · simp only [haltonPi, Sg, coeff_neg, coeff_sum_X_pow, ← he]; rw [ite_eq_left (by omega)]; rfl

/-! ## Faure sequences and unscrambled frames -/

section Faure
variable {F : Type*} [Field F]

/-- The Taylor digits at `a` are the `(z - a)`-adic digits: `[(z-a)^n] V = [z^0] a_n(V)`. -/
theorem taylor_coeff_eq_badicDigit (a : F) (V : F[X]) (n : ℕ) :
    (taylor a V).coeff n = (badicDigit (X - C a) V n).coeff 0 := by
  set B := (X - C a) ^ n with hB
  have hB0 : B ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero a)
  have hdiv : B * (V / B) + V % B = V := EuclideanDomain.div_add_mod V B
  have hr : (V % B).degree < B.degree := degree_mod_lt _ hB0
  have hnB : B.natDegree = n := by rw [hB, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hta : taylor a (X - C a) = X := by rw [map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  have hrn : (taylor a (V % B)).coeff n = 0 := by
    by_cases h0 : V % B = 0
    · rw [h0, map_zero, coeff_zero]
    · apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_taylor, ← hnB]
      exact natDegree_lt_natDegree h0 hr
  conv_lhs => rw [← hdiv]
  rw [map_add, taylor_mul, hB, taylor_pow, hta, coeff_add, hrn, add_zero, coeff_X_pow_mul',
    ite_eq_left le_rfl, Nat.sub_self, taylor_coeff_zero, badicDigit, ← hB, mod_X_sub_C_eq_C_eval, coeff_C_zero]

end Faure

section FaureSeq
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- The unscrambled frame `(P_{a_0}, …, P_{a_{s-1}})` is the Halton-type sequence in the bases `z - a_c`. -/
theorem frame_eq_haltonPt (a : Fin s → ZMod p) :
    seqPoint (zcode p) (fun c n k => pas (a c) n k) = haltonPt p (fun c => X - C (a c)) := by
  rw [haltonPt_eq_linPt _ (fun c => by rw [natDegree_X_sub_C])]
  funext v c
  unfold seqPoint seqCoord linPt
  refine tsum_congr fun n => ?_
  congr 3
  have h1 : seqDigit (zcode p) (fun c n k => pas (a c) n k) v c n =
      (taylor (a c) (idxPolyP p v)).coeff n := by
    have hv : idxPolyP p v = vecPoly (fun k => idxDigit (zcode p) v k) (v + 1) := by
      unfold idxPolyP vecPoly
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← C_mul_X_pow_eq_monomial]; rfl
    rw [hv, taylor_coeff_vecPoly]
    rfl
  rw [show ((zcode p).enc (seqDigit (zcode p) (fun c n k => pas (a c) n k) v c n) : ℕ) =
      (seqDigit (zcode p) (fun c n k => pas (a c) n k) v c n).val from rfl, h1,
    taylor_coeff_eq_badicDigit]
  simp only [haltonY, haltonPi, natDegree_X_sub_C, Nat.div_one, Nat.mod_one, Nat.sub_self]

/-- **`cor:faure`** (prime `q = p`). For every `s ≥ 2` and all distinct places `a_0, …, a_{s-1} ∈ 𝔽_p` (so
`s ≤ p`), the unscrambled frame sequence `(P_{a_0}, …, P_{a_{s-1}})` has, for every `ε > 0`, a prefix `P_m` with two
points at distance `< ε p^{-m/s}`, and is not quasi-uniform. -/
theorem faure_not_quasiUniform (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (seqPoint (zcode p) (fun c n k => pas (a c) n k) v)
          (seqPoint (zcode p) (fun c n k => pas (a c) n k) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (seqPoint (zcode p) (fun c n k => pas (a c) n k)) := by
  rw [frame_eq_haltonPt]
  exact halton_not_quasiUniform p s hs _ (fun c => by rw [natDegree_X_sub_C])
    (fun c c' h => pairwise_coprime_X_sub_C ha h)

/-- **`cor:faure`**, "in particular": the Faure sequence `(P^0, P^1, …, P^{s-1})` in prime base `p`
(`P^c[n][k] = C(k, n) c^{k-n}`, the frame at the places `0, 1, …, s-1`) is not quasi-uniform for every
`2 ≤ s ≤ p`. -/
theorem faureSeq_not_quasiUniform (hs : 2 ≤ s) (hsp : s ≤ p) :
    ¬ IsQuasiUniform (seqPoint (zcode p) (fun (c : Fin s) n k => pas (faurePlace p c : ZMod p) n k)) :=
  (faure_not_quasiUniform hs _ (faurePlace_injective hsp)).2

end FaureSeq

end GeoSeq
