/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Sobol

@[expose] public section

/-!
# GeoSeq stage V9-5 (part 3): Niederreiter sequences (`lem:nied`, `cor:nied`)

Monic bases `b` of degree `e ≥ 1`; `[z^{-1}] ϑ V / b^{Q+1}` is `niedDigit` (`V9Defs`-style remainder formula).

* `niedY_lin`, **`nied_isBAdic`** (`lem:nied`, first sentence): every Niederreiter coordinate is `b`-adic.
* `nied_top`: the coefficient of `z^{(Q+1)e-1}` in `(f + b^Q r) mod b^{Q+1}` is `[z^{e-1}] r` for `deg f ≤ (Q+1)e - 2`,
  `deg r < e` (the computation of the proof of `lem:nied`).
* **`nied_digit`** (`lem:nied`, second sentence): under `ϑ_{Q,i} ≡ ϑ̄_i (mod b^{Q+1})` (`ϑ̄_i = ϑ_{0,i} mod b`), digit
  block `Q` is `π(a_Q)`, `π(a)_i = [z^{-1}] ϑ̄_i a / b`.
* **`niedPi_onto`** (the pairing is nondegenerate): for irreducible `b` over a finite field and `ϑ_{0,0}, …, ϑ_{0,e-1}`
  linearly independent modulo `b`, `π` maps the polynomials of degree `< e` onto `𝔽^e`; **`nied_radInv`**: the
  coordinate is a `b`-adic radical inverse; `classical_*`: the classical sequence (`ϑ_{Q,i} = z^i`) satisfies both.
* **`nied_not_qu`**, **`niedGen_not_qu`** (`cor:nied`, prime field, natural identification): every classical
  Niederreiter sequence (`s ≥ 2`, distinct monic irreducible bases) is not quasi-uniform; so is every generalized one
  with one coordinate `ĉ` of the stated form, whatever the polynomials of the other coordinates.
-/

namespace GeoSeq

open Finset Polynomial

section Field
variable {F : Type*} [Field F]

theorem niedY_lin (b : F[X]) (ϑ : ℕ → ℕ → F[X]) : IsLinCoord (niedY b ϑ) := by
  intro V W n
  simp only [niedY, niedDigit, mul_add, add_modByMonic, coeff_add]

/-- **`lem:nied`** (first sentence): a Niederreiter coordinate with monic base `b` (degree `≥ 1`) is `b`-adic. -/
theorem nied_isBAdic (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (ϑ : ℕ → ℕ → F[X]) :
    IsBAdic (niedY b ϑ) b := by
  intro Q V hV n hn
  have hQ : n / b.natDegree + 1 ≤ Q := by
    have := Nat.div_lt_iff_lt_mul (by omega : 0 < b.natDegree) |>.mpr (by rw [mul_comm]; exact hn); omega
  unfold niedY niedDigit
  rw [(modByMonic_eq_zero_iff_dvd (hb.pow _)).mpr, coeff_zero]
  exact dvd_mul_of_dvd_right ((pow_dvd_pow b hQ).trans hV) _

/-- The coefficient computation of `lem:nied`: for monic `b` of degree `e`, `deg f ≤ (Q+1)e - 2` (or `f = 0`) and
`deg r < e`, the coefficient of `z^{(Q+1)e - 1}` in `(f + b^Q r) mod b^{Q+1}` is `[z^{e-1}] r`. -/
theorem nied_top (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (Q : ℕ) (f r : F[X])
    (hf : f = 0 ∨ f.natDegree + 2 ≤ (Q + 1) * b.natDegree) (hr : r.natDegree < b.natDegree) :
    ((f + b ^ Q * r) %ₘ b ^ (Q + 1)).coeff ((Q + 1) * b.natDegree - 1) = r.coeff (b.natDegree - 1) := by
  set e := b.natDegree with hedef
  have hbQ : (b ^ Q).natDegree = Q * e := by rw [(hb).natDegree_pow]
  have hbQ1 : (b ^ (Q + 1)).natDegree = (Q + 1) * e := by rw [(hb).natDegree_pow]
  have hdeg2 : (b ^ Q * r).natDegree ≤ (Q + 1) * e - 1 :=
    natDegree_mul_le.trans (by rw [hbQ]; have : (Q + 1) * e = Q * e + e := (by ring); omega)
  have hfdeg : f.natDegree ≤ (Q + 1) * e - 1 := by
    rcases hf with rfl | hf
    · simp
    · omega
  have hN : (f + b ^ Q * r).natDegree < (Q + 1) * e := by
    have := natDegree_add_le f (b ^ Q * r)
    have : (Q + 1) * e ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hlt : (f + b ^ Q * r).degree < (b ^ (Q + 1)).degree := by
    rw [degree_eq_natDegree ((hb.pow _).ne_zero), hbQ1]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast hN)
  rw [(modByMonic_eq_self_iff (hb.pow _)).mpr hlt, coeff_add]
  have hf0 : f.coeff ((Q + 1) * e - 1) = 0 := by
    rcases hf with rfl | hf
    · simp
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hsplit : (Q + 1) * e - 1 = Q * e + (e - 1) := by
    have : (Q + 1) * e = Q * e + e := by ring
    omega
  rw [hf0, zero_add, hsplit, coeff_mul_add_eq_of_natDegree_le hbQ.le (by omega)]
  have := (hb.pow Q).coeff_natDegree
  rw [hbQ] at this
  rw [this, one_mul]

/-- **`lem:nied`** (second sentence, digit computation): if `ϑ_{Q,i} ≡ ϑ̄_i (mod b^{Q+1})` for all `Q` and `i < e`,
`ϑ̄_i = ϑ_{0,i} mod b`, then digit `Q e + i` is `π(a_Q)_i = [z^{-1}] ϑ̄_i a_Q / b`, `a_Q` the `Q`-th `b`-adic digit. -/
theorem nied_digit (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (ϑ : ℕ → ℕ → F[X])
    (hcong : ∀ Q i, i < b.natDegree → b ^ (Q + 1) ∣ ϑ Q i - ϑ 0 i %ₘ b) (V : F[X]) (Q i : ℕ)
    (hi : i < b.natDegree) :
    niedY b ϑ V (Q * b.natDegree + i) = niedPi b (ϑ 0) (badicDigit b V Q) i := by
  set e := b.natDegree with hedef
  have hb0 : b ≠ 0 := hb.ne_zero
  have hdiv : (Q * e + i) / e = Q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, zero_add]
  have hmod : (Q * e + i) % e = i := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  set tb := ϑ 0 i %ₘ b with htb
  have htbdeg : tb.natDegree < e := by
    have := degree_modByMonic_lt (ϑ 0 i) hb
    rcases eq_or_ne tb 0 with h0 | h0
    · rw [h0, natDegree_zero]; omega
    · exact (natDegree_lt_natDegree h0 this)
  -- replace `ϑ_{Q,i}` by `ϑ̄_i`
  unfold niedY niedDigit
  rw [hdiv, hmod, modByMonic_eq_of_dvd_sub (hb.pow _) (show b ^ (Q + 1) ∣ ϑ Q i * V - tb * V by
    rw [← sub_mul]; exact dvd_mul_of_dvd_left (hcong Q i hi) V)]
  -- `V = V mod b^Q + b^Q a_Q + b^{Q+1} W`
  set aQ := badicDigit b V Q with haQ
  set W := V / b ^ Q / b with hW
  have hV : V = V % b ^ Q + b ^ Q * aQ + b ^ (Q + 1) * W := by
    have h1 := EuclideanDomain.div_add_mod V (b ^ Q)
    have h2 := EuclideanDomain.div_add_mod (V / b ^ Q) b
    rw [haQ, badicDigit, hW, pow_succ]
    linear_combination (-1 : F[X]) * h1 + (-(b ^ Q)) * h2
  have haQdeg : aQ.natDegree < e := natDegree_mod_lt _ (by omega)
  set r := (tb * aQ) %ₘ b with hr
  set t := (tb * aQ) /ₘ b with ht
  have hrt : tb * aQ = r + b * t := (modByMonic_add_div (tb * aQ) b).symm
  have hrdeg : r.natDegree < e := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, natDegree_zero]; omega
    · exact natDegree_lt_natDegree h0 (degree_modByMonic_lt _ hb)
  have hsum : tb * V = (tb * (V % b ^ Q) + b ^ Q * r) + b ^ (Q + 1) * (t + tb * W) := by
    conv_lhs => rw [hV]
    rw [pow_succ]
    linear_combination (b ^ Q) * hrt
  rw [hsum, add_modByMonic, (modByMonic_eq_zero_iff_dvd (hb.pow _)).mpr (dvd_mul_right _ _), add_zero,
    nied_top b hb he Q _ r ?_ hrdeg]
  · rw [niedPi, hr, modByMonic_eq_of_dvd_sub hb (show b ∣ tb * aQ - ϑ 0 i * aQ from
      ⟨-(ϑ 0 i /ₘ b) * aQ, by rw [htb]; linear_combination aQ * modByMonic_add_div (ϑ 0 i) b⟩)]
  · rcases Nat.eq_zero_or_pos Q with hQ | hQ
    · left; rw [hQ, pow_zero, EuclideanDomain.mod_one, mul_zero]
    · rcases eq_or_ne (V % b ^ Q) 0 with h0 | h0
      · left; rw [h0, mul_zero]
      · right
        have h1 : (V % b ^ Q).natDegree < Q * e := by
          have := natDegree_mod_lt V (q := b ^ Q) (by rw [hb.natDegree_pow]; positivity)
          rw [hb.natDegree_pow] at this
          rw [hedef]; exact this
        have h2 := natDegree_mul_le (p := tb) (q := V % b ^ Q)
        have : (Q + 1) * e = Q * e + e := by ring
        have h3 : (Q + 1) * b.natDegree = Q * e + e := by rw [← hedef]; ring
        omega

end Field

section Finite
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma niedPi_add (b : F[X]) (ϑ0 : ℕ → F[X]) (a a' : F[X]) (i : ℕ) :
    niedPi b ϑ0 (a + a') i = niedPi b ϑ0 a i + niedPi b ϑ0 a' i := by
  simp only [niedPi, mul_add, add_modByMonic, coeff_add]

lemma vecPolyG_coeff (e : ℕ) (v : Fin e → F) (m : ℕ) :
    (∑ j : Fin e, C (v j) * X ^ (j : ℕ)).coeff m = if h : m < e then v ⟨m, h⟩ else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with hm
  · rw [Finset.sum_eq_single ⟨m, hm⟩ (fun x _ hx => if_neg fun h' => hx (Fin.ext h'.symm)) (by simp),
      if_pos rfl]
  · exact Finset.sum_eq_zero fun x _ => if_neg fun (h' : m = (x : ℕ)) => hm (h' ▸ x.isLt)

lemma vecPolyG_natDegree (e : ℕ) (he : 1 ≤ e) (v : Fin e → F) :
    (∑ j : Fin e, C (v j) * X ^ (j : ℕ)).natDegree < e := by
  rw [Nat.lt_iff_le_pred he]
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := j.isLt; omega

/-- **The pairing of `lem:nied` is nondegenerate**: for irreducible monic `b` of degree `e ≥ 1` over a finite field and
`ϑ_{0,0}, …, ϑ_{0,e-1}` linearly independent modulo `b`, the digit map `π(a)_i = [z^{-1}] ϑ_{0,i} a / b` maps the
polynomials of degree `< e` onto `𝔽^e`. -/
theorem niedPi_onto (b : F[X]) (hb : b.Monic) (hirr : Irreducible b) (he : 1 ≤ b.natDegree)
    (ϑ0 : ℕ → F[X]) (hind : ∀ κ : Fin b.natDegree → F, b ∣ ∑ i, C (κ i) * ϑ0 i → κ = 0) (w : ℕ → F) :
    ∃ a : F[X], a.natDegree < b.natDegree ∧ ∀ i, i < b.natDegree → niedPi b ϑ0 a i = w i := by
  set e := b.natDegree with hedef
  -- (i) every polynomial is `≡ ∑ κ_i ϑ_{0,i}` modulo `b`
  let A : (Fin e → F) → (Fin e → F) := fun κ j => ((∑ i, C (κ i) * ϑ0 i) %ₘ b).coeff j
  have hAinj : Function.Injective A := by
    intro κ κ' h
    have hm : (∑ i, C (κ i) * ϑ0 i) %ₘ b = (∑ i, C (κ' i) * ϑ0 i) %ₘ b := by
      ext j
      by_cases hj : j < e
      · exact congrFun h ⟨j, hj⟩
      · have h1 := degree_modByMonic_lt (∑ i, C (κ i) * ϑ0 i) hb
        have h2 := degree_modByMonic_lt (∑ i, C (κ' i) * ϑ0 i) hb
        rw [degree_eq_natDegree hb.ne_zero] at h1 h2
        rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h1 (by exact_mod_cast (by omega : e ≤ j))),
          coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h2 (by exact_mod_cast (by omega : e ≤ j)))]
    have hd : b ∣ ∑ i, C ((κ - κ') i) * ϑ0 i := by
      have e1 : ∑ i, C ((κ - κ') i) * ϑ0 i = ∑ i, C (κ i) * ϑ0 i - ∑ i, C (κ' i) * ϑ0 i := by
        simp [sub_mul, Finset.sum_sub_distrib]
      rw [e1]; apply (modByMonic_eq_zero_iff_dvd hb).mp; rw [sub_modByMonic, hm, sub_self]
    exact sub_eq_zero.mp (hind _ hd)
  have hAsurj := Finite.surjective_of_injective hAinj
  have hrep : ∀ f : F[X], ∃ κ : Fin e → F, (∑ i, C (κ i) * ϑ0 i) %ₘ b = f %ₘ b := by
    intro f
    obtain ⟨κ, hκ⟩ := hAsurj fun j => (f %ₘ b).coeff j
    refine ⟨κ, ?_⟩
    ext j
    by_cases hj : j < e
    · exact congrFun hκ ⟨j, hj⟩
    · have h1 := degree_modByMonic_lt (∑ i, C (κ i) * ϑ0 i) hb
      have h2 := degree_modByMonic_lt f hb
      rw [degree_eq_natDegree hb.ne_zero] at h1 h2
      rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h1 (by exact_mod_cast (by omega : e ≤ j))),
        coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h2 (by exact_mod_cast (by omega : e ≤ j)))]
  -- (ii) `π` is injective on the polynomials of degree `< e`
  let Pm : (Fin e → F) → (Fin e → F) := fun v i => niedPi b ϑ0 (∑ j : Fin e, C (v j) * X ^ (j : ℕ)) i
  have hPminj : Function.Injective Pm := by
    intro v v' hvv
    by_contra hne
    set a : F[X] := ∑ j : Fin e, C (v j) * X ^ (j : ℕ) - ∑ j : Fin e, C (v' j) * X ^ (j : ℕ) with ha
    have ha0 : a ≠ 0 := by
      intro h0; apply hne; funext j
      have := congrArg (fun f => f.coeff j) h0
      simp only [ha, coeff_sub, vecPolyG_coeff, dif_pos j.isLt, coeff_zero] at this
      exact sub_eq_zero.mp this
    have hadeg : a.natDegree < e := lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (vecPolyG_natDegree e he v) (vecPolyG_natDegree e he v'))
    have hπa : ∀ i : Fin e, niedPi b ϑ0 a i = 0 := by
      intro i
      have h1 := niedPi_add b ϑ0 a (∑ j : Fin e, C (v' j) * X ^ (j : ℕ)) i
      rw [show a + ∑ j : Fin e, C (v' j) * X ^ (j : ℕ) = ∑ j : Fin e, C (v j) * X ^ (j : ℕ) by
        simp [ha]] at h1
      have h2 := congrFun hvv i
      simp only [Pm] at h2
      rw [h2] at h1
      linear_combination -h1
    -- `b ∤ a`, so `f a ≡ z^{e-1}` for some `f`
    have hcop : IsCoprime b a := (Irreducible.coprime_iff_not_dvd hirr).mpr fun hd => by
      have := natDegree_le_of_dvd hd ha0; omega
    obtain ⟨g, f, hfg⟩ := hcop
    obtain ⟨κ, hκ⟩ := hrep (X ^ (e - 1) * f)
    have hdX : ((X : F[X]) ^ (e - 1)).degree < b.degree := by
      rw [degree_X_pow, degree_eq_natDegree hb.ne_zero]; exact_mod_cast (by omega : e - 1 < e)
    have hval : ((∑ i, C (κ i) * ϑ0 i) * a %ₘ b).coeff (e - 1) = 1 := by
      have h1 : (∑ i, C (κ i) * ϑ0 i) * a %ₘ b = (X ^ (e - 1) * f * a) %ₘ b := by
        rw [mul_modByMonic, hκ, ← mul_modByMonic]
      have h2 : (X : F[X]) ^ (e - 1) * f * a = X ^ (e - 1) - b * (X ^ (e - 1) * g) := by
        linear_combination (X : F[X]) ^ (e - 1) * hfg
      have h3 : ((X : F[X]) ^ (e - 1) - b * (X ^ (e - 1) * g)) %ₘ b = X ^ (e - 1) := by
        rw [sub_modByMonic, (modByMonic_eq_zero_iff_dvd hb).mpr (dvd_mul_right _ _), sub_zero,
          (modByMonic_eq_self_iff hb).mpr hdX]
      rw [h1, h2, h3, coeff_X_pow_self]
    have hzero : ((∑ i, C (κ i) * ϑ0 i) * a %ₘ b).coeff (e - 1) = 0 := by
      rw [Finset.sum_mul, ← modByMonicHom_apply, map_sum, finsetSum_coeff]
      simp only [modByMonicHom_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mul_assoc, ← smul_eq_C_mul, smul_modByMonic, coeff_smul]
      have := hπa i
      simp only [niedPi] at this
      rw [this, smul_zero]
    exact one_ne_zero (hval.symm.trans hzero)
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hPminj (fun i => w i)
  exact ⟨∑ j : Fin e, C (v j) * X ^ (j : ℕ), vecPolyG_natDegree e he v, fun i hi => congrFun hv ⟨i, hi⟩⟩

/-- **`lem:nied`** (second sentence): under the congruence, with `b` monic irreducible and `ϑ_{0,i}` (`i < e`)
linearly independent modulo `b`, the Niederreiter coordinate is a `b`-adic radical inverse with digit map
`π(a)_i = [z^{-1}] ϑ_{0,i} a / b`. -/
theorem nied_radInv (b : F[X]) (hb : b.Monic) (hirr : Irreducible b) (he : 1 ≤ b.natDegree)
    (ϑ : ℕ → ℕ → F[X]) (hcong : ∀ Q i, i < b.natDegree → b ^ (Q + 1) ∣ ϑ Q i - ϑ 0 i %ₘ b)
    (hind : ∀ κ : Fin b.natDegree → F, b ∣ ∑ i, C (κ i) * ϑ 0 i → κ = 0) :
    IsRadInv (niedY b ϑ) b (niedPi b (ϑ 0)) :=
  ⟨niedPi_onto b hb hirr he (ϑ 0) hind, fun V Q i hi => nied_digit b hb he ϑ hcong V Q i hi⟩

/-- The classical Niederreiter coordinate (`ϑ_{Q,i} = z^i`) satisfies the congruence of `lem:nied`. -/
lemma classical_cong (b : F[X]) (hb : b.Monic) (Q i : ℕ) (hi : i < b.natDegree) :
    b ^ (Q + 1) ∣ (fun (_ i : ℕ) => (X : F[X]) ^ i) Q i - (fun (_ i : ℕ) => (X : F[X]) ^ i) 0 i %ₘ b := by
  simp only
  have hd : ((X : F[X]) ^ i).degree < b.degree := by
    rw [degree_X_pow, degree_eq_natDegree hb.ne_zero]; exact_mod_cast hi
  rw [(modByMonic_eq_self_iff hb).mpr hd, sub_self]
  exact dvd_zero _

/-- `1, z, …, z^{e-1}` are linearly independent modulo `b` (`deg b = e`). -/
lemma classical_ind (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (κ : Fin b.natDegree → F)
    (h : b ∣ ∑ i, C (κ i) * (fun (_ i : ℕ) => (X : F[X]) ^ i) 0 i) : κ = 0 := by
  simp only at h
  have hz : ∑ i : Fin b.natDegree, C (κ i) * X ^ (i : ℕ) = 0 := by
    by_contra h0
    have := natDegree_le_of_dvd h h0
    have := vecPolyG_natDegree b.natDegree he κ
    omega
  funext j
  have := congrArg (fun f => f.coeff j) hz
  simp only [vecPolyG_coeff, dif_pos j.isLt, coeff_zero] at this
  exact this

end Finite

section Main
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- Distinct monic irreducible polynomials are pairwise coprime. -/
lemma monic_irred_coprime {F : Type*} [Field F] (b : Fin s → F[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) :
    Pairwise fun c c' => IsCoprime (b c) (b c') := by
  intro c c' hcc
  refine (Irreducible.coprime_iff_not_dvd (hirr c)).mpr fun hd => hinj.ne hcc ?_
  exact eq_of_monic_of_associated (hm c) (hm c') (Irreducible.associated_of_dvd (hirr c) (hirr c') hd)

/-- **`cor:nied`** (generalized form): let the bases `b_c ∈ 𝔽_p[z]` be distinct monic irreducible, let every
coordinate be a generalized Niederreiter coordinate `niedY b_c ϑ_c` (arbitrary polynomials `ϑ_c`), and let one
coordinate `ĉ` satisfy `ϑ_{ĉ,Q,i} ≡ ϑ̄_{ĉ,i} (mod b_ĉ^{Q+1})` with `ϑ_{ĉ,0,i}` linearly independent modulo `b_ĉ`.
Then the sequence is not quasi-uniform (and has close pairs at prefixes `P_m`). -/
theorem niedGen_not_qu (hs : 2 ≤ s) (b : Fin s → (ZMod p)[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) (ϑ : Fin s → ℕ → ℕ → (ZMod p)[X])
    (ch : Fin s) (hcong : ∀ Q i, i < (b ch).natDegree → b ch ^ (Q + 1) ∣ ϑ ch Q i - ϑ ch 0 i %ₘ b ch)
    (hind : ∀ κ : Fin (b ch).natDegree → ZMod p, b ch ∣ ∑ i, C (κ i) * ϑ ch 0 i → κ = 0) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (linPt p (fun c => niedY (b c) (ϑ c)) v) (linPt p (fun c => niedY (b c) (ϑ c)) w) <
          ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPt p fun c => niedY (b c) (ϑ c)) := by
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := fun c =>
    Nat.one_le_iff_ne_zero.mpr fun h => (hirr c).not_isUnit (by
      rw [eq_one_of_monic_natDegree_zero (hm c) h]; exact isUnit_one)
  exact nonqu hs _ (fun c => niedY_lin _ _) b hdeg (monic_irred_coprime b hm hirr hinj) ch
    (fun c _ => nied_isBAdic (b c) (hm c) (hdeg c) (ϑ c)) _
    (nied_radInv (b ch) (hm ch) (hirr ch) (hdeg ch) (ϑ ch) hcong hind)

/-- **`cor:nied`** (classical): every classical Niederreiter sequence over `𝔽_p` (`s ≥ 2`, distinct monic
irreducible bases, `ϑ_{c,Q,i} = z^i`, natural identification) is not quasi-uniform. -/
theorem nied_not_qu (hs : 2 ≤ s) (b : Fin s → (ZMod p)[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) :
    ¬ IsQuasiUniform (linPt p fun c => niedY (b c) (fun _ i => X ^ i)) := by
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := fun c =>
    Nat.one_le_iff_ne_zero.mpr fun h => (hirr c).not_isUnit (by
      rw [eq_one_of_monic_natDegree_zero (hm c) h]; exact isUnit_one)
  have ch : Fin s := ⟨0, by omega⟩
  exact (niedGen_not_qu hs b hm hirr hinj (fun _ _ i => X ^ i) ch
    (fun Q i hi => classical_cong (b ch) (hm ch) Q i hi)
    (fun κ h => classical_ind (b ch) (hm ch) (hdeg ch) κ h)).2

end Main

end GeoSeq
