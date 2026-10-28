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
# GeoSeq stage V4: ordered designs (`thm:LF`(a), `app:LFdata`)

* `od_kap`: the crosses of an ordered design are the integers `odK` (`lem:cauchy`: `λ_c = θ^c/Q_{0c}`).
* `od_cover`: every column covers (`lem:ws` in the stored row order; `lem:lexcover`).
* **`od_sound`**: `thm:MR` holds verbatim for every valid ordered design (`odValid`): selection rules exist and
  every selection rule gives a quasi-uniform digital `(0,s)`-sequence with `c(P_{sK}) ≥ (p - Γ)/p`, every `K`.
* `od_seq`: a valid ordered design gives such a sequence (existential form).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {s : ℕ}

/-! ## Row orders -/

section Perm

variable (D : ODesign s)

lemma od_mem (hord : ∀ j < s, (D.ord.getD j []).length = j ∧ (D.ord.getD j []).Nodup ∧
      ∀ x ∈ D.ord.getD j [], x < j) {c j : ℕ} (hj : j < s) (hc : c < j) : c ∈ D.ord.getD j [] := by
  classical
  obtain ⟨hlen, hnd, hlt⟩ := hord j hj
  have hsub : (D.ord.getD j []).toFinset ⊆ range j := fun x hx =>
    mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_range, List.toFinset_card_of_nodup hnd, hlen])
  have : c ∈ (D.ord.getD j []).toFinset := by rw [heq]; exact mem_range.mpr hc
  exact List.mem_toFinset.mp this

variable (hord : ∀ j < s, (D.ord.getD j []).length = j ∧ (D.ord.getD j []).Nodup ∧
      ∀ x ∈ D.ord.getD j [], x < j)
include hord

lemma od_pos_lt {c j : ℕ} (hj : j < s) (hc : c < j) : odPos D c j < j := by
  have := List.idxOf_lt_length_iff.mpr (od_mem D hord hj hc)
  rwa [(hord j hj).1] at this

lemma od_row_pos {c j : ℕ} (hj : j < s) (hc : c < j) : odRow D j (odPos D c j) = c := by
  have h := List.idxOf_lt_length_iff.mpr (od_mem D hord hj hc)
  unfold odRow odPos
  rw [List.getD_eq_getElem _ _ h, List.getElem_idxOf h]

lemma od_row_lt {j t : ℕ} (hj : j < s) (ht : t < j) : odRow D j t < j := by
  have h : t < (D.ord.getD j []).length := by rw [(hord j hj).1]; exact ht
  unfold odRow
  rw [List.getD_eq_getElem _ _ h]
  exact (hord j hj).2.2 _ (List.getElem_mem h)

lemma od_pos_row {j t : ℕ} (hj : j < s) (ht : t < j) : odPos D (odRow D j t) j = t := by
  have h : t < (D.ord.getD j []).length := by rw [(hord j hj).1]; exact ht
  unfold odRow odPos
  rw [List.getD_eq_getElem _ _ h, List.Nodup.idxOf_getElem (hord j hj).2.1]

end Perm

/-! ## Windows -/

section Bounds

variable {D : ODesign s} {p : ℕ}

lemma odCost_ge (c : ℕ) (hc : c < s) : 2 * odB D p c + odM D p c ≤ odCost D p :=
  Finset.le_sup (f := fun c => 2 * odB D p c + odM D p c) (mem_range.mpr hc)

lemma odBx_le_odB (c j : ℕ) (hcj : c < j) (hj : j < s) : odBx D p c j ≤ odB D p c :=
  Finset.single_le_sum (f := fun j => odBx D p c j) (fun _ _ => Nat.zero_le _) (mem_Ioo.mpr ⟨hcj, hj⟩)

lemma odNu_le_odBp (j t : ℕ) : odNu D j t ≤ odBp D p j t := by
  unfold odBp
  split_ifs with h0
  · subst h0; exact le_rfl
  · exact le_max_left _ _

lemma odN_eq_wsN (j : ℕ) : ∀ t, odN D p j t =
    wsN p (fun t => 2 * odBp D p j t + 1) (fun t => odNu D j t) t := by
  intro t
  induction t with
  | zero => simp [odN, wsN, odBp, Nat.sub_sub]
  | succ t ih => simp only [odN, wsN, ih]

lemma odN_pos (hp : 1 ≤ p) (j : ℕ) (hν : ∀ t, t < j → 1 ≤ odNu D j t) : ∀ t, t < j → 1 ≤ odN D p j t := by
  intro t
  induction t with
  | zero => intro _; simp [odN]
  | succ t ih =>
    intro ht
    simp only [odN]
    have := ih (by omega)
    have := cdiv_pos p _ hp (hν (t + 1) ht)
    omega

lemma odM_pos (hp : 1 ≤ p) (j : ℕ) (hν : ∀ t, t < j → 1 ≤ odNu D j t) : 1 ≤ odM D p j := by
  unfold odM
  split_ifs with h0
  · exact le_rfl
  · exact odN_pos hp j hν (j - 1) (by omega)

lemma od_row_lt_p (hΓ : odCost D p < p) (c : ℕ) (hc : c < s) : 2 * odB D p c + odM D p c < p :=
  lt_of_le_of_lt (odCost_ge c hc) hΓ

lemma odB_eq_lexB (c : Fin s) : lexB (fun c j : Fin s => odBx D p c j) c = odB D p c := by
  classical
  unfold lexB odB
  rw [Finset.sum_filter]
  have e : ∀ c' : Fin s, (if c < c' then odBx D p c c' else 0) =
      (fun j : ℕ => if (c : ℕ) < j then odBx D p c j else 0) c' := fun c' => by
    simp only [Fin.lt_iff_val_lt_val]
  rw [Finset.sum_congr rfl (fun c' _ => e c'),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if (c : ℕ) < j then odBx D p c j else 0) s,
    ← Finset.sum_filter]
  congr 1; ext j; simp only [mem_filter, mem_range, mem_Ioo]; omega

lemma od_lexCost : lexCost (fun c : Fin s => odB D p c) (fun c => odM D p c)
    (fun c j => odBx D p c j) = odCost D p := by
  have e : lexCost (fun c : Fin s => odB D p c) (fun c => odM D p c)
      (fun c j => odBx D p c j) = univ.sup fun c : Fin s => 2 * odB D p c + odM D p c := by
    unfold lexCost; congr 1; funext c; rw [odB_eq_lexB]; ring
  rw [e]
  apply le_antisymm
  · exact Finset.sup_le fun c _ => odCost_ge (D := D) (p := p) c c.isLt
  · unfold odCost
    refine Finset.sup_le fun c hc => ?_
    have := Finset.le_sup (f := fun c : Fin s => 2 * odB D p c + odM D p c)
      (mem_univ (⟨c, mem_range.mp hc⟩ : Fin s))
    exact this

end Bounds

/-! ## The crosses -/

section Kap

variable {p : ℕ} [Fact p.Prime]

lemma kap_alg {F : Type*} [Field F] (θ W Δ Pc Q K n d : F) (c e : ℕ) (hθ : θ = n / d) (hn : n ≠ 0)
    (hd : d ≠ 0) (hW : W ≠ 0) (hΔ : Δ ≠ 0) (hP : Pc ≠ 0) (hQ : Q ≠ 0)
    (hK : d ^ e * Q = K * (n ^ e * W * Δ)) :
    θ * (θ ^ c / Pc) / ((θ ^ (c + 1 + e) / (Pc * Q)) * W * Δ) = K := by
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact div_ne_zero hn hd
  have h1 : θ * (θ ^ c / Pc) / ((θ ^ (c + 1 + e) / (Pc * Q)) * W * Δ) = Q / (θ ^ e * W * Δ) := by
    rw [pow_add, pow_add, pow_one]; field_simp
  rw [h1, hθ, div_pow, div_eq_iff (by simp [hn, hd, hW, hΔ])]
  field_simp
  linear_combination hK

lemma odQ_ne (D : ODesign s) (hv : odValid p D) (a b : ℕ) (hb : b < s) : (odQ D a b : ZMod p) ≠ 0 := by
  obtain ⟨-, hd, -, -, hsup, -, -⟩ := hv
  unfold odQ
  push_cast
  rw [prod_ne_zero_iff]
  intro i hi
  have hi1 := (mem_Ico.mp hi).2
  unfold odFac
  push_cast
  refine mul_ne_zero (mul_ne_zero (intCast_ne_zero_of_emod (hsup (i + 1) (by omega) (by omega)).2)
    (frameW_ne s D.frame hd (by omega))) (sub_ne_zero.mpr ?_)
  exact frame_ne s D.frame hd (by omega) (by omega) (by omega)

lemma odTheta_ne (D : ODesign s) (hv : odValid p D) : odTheta D p ≠ 0 :=
  div_ne_zero (intCast_ne_zero_of_emod hv.2.2.1) (intCast_ne_zero_of_emod hv.2.2.2.1)

lemma odLam_ne (D : ODesign s) (hv : odValid p D) (c : Fin s) : odLam D p c ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (odTheta_ne D hv)) (odQ_ne D hv 0 c c.isLt)

/-- **The crosses of an ordered design** (`lem:cauchy`): with `λ_c = θ^c/Q_{0c}`, the upper crosses are the
integers `κ_{c←j} = odK D c j`. -/
theorem od_kap (D : ODesign s) (hv : odValid p D) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.frame c : ℤ) : ZMod p)) (c j : Fin s) (hcj : c < j) :
    kapL (odTheta D p) (odLam D p) zθ c j = (odK D c j : ZMod p) := by
  have hv' := hv
  obtain ⟨-, hd, hn, hdd, -, hint, -⟩ := hv'
  have hcj' : (c : ℕ) < j := hcj
  obtain ⟨e, he⟩ : ∃ e, (j : ℕ) = c + 1 + e := ⟨j - c - 1, by omega⟩
  have hdiv : odDen D c j ∣ odNum D c j := Int.dvd_of_emod_eq_zero (hint j j.isLt c hcj').1
  have hK0 : odK D c j * odDen D c j = odNum D c j := Int.ediv_mul_cancel hdiv
  have hK := congrArg (fun z : ℤ => (z : ZMod p)) hK0
  simp only [odNum, odDen, show (j : ℕ) - c - 1 = e by omega] at hK
  push_cast at hK
  unfold kapL odLam
  rw [frame_placeDer s D.frame zθ hplace c]
  simp only [ssPlace, hplace]
  have hsplit : odQ D 0 (c + 1 + e) = odQ D 0 c * odQ D c (c + 1 + e) := by
    unfold odQ
    rw [Finset.prod_Ico_consecutive _ (Nat.zero_le (c : ℕ)) (show (c : ℕ) ≤ c + 1 + e by omega)]
  rw [he, hsplit]
  change odTheta D p * (odTheta D p ^ (c : ℕ) / (odQ D 0 c : ZMod p)) /
    (odTheta D p ^ (c + 1 + e) / (((odQ D 0 c * odQ D c (c + 1 + e) : ℤ)) : ZMod p) *
      ((frameW s D.frame c : ℤ) : ZMod p) *
      (((frameA D.frame (c + 1 + e) : ℤ) : ZMod p) - ((frameA D.frame c : ℤ) : ZMod p))) = _
  push_cast
  rw [he] at hK
  refine kap_alg _ _ _ _ _ _ (D.thn : ZMod p) (D.thd : ZMod p) c e rfl (intCast_ne_zero_of_emod hn)
    (intCast_ne_zero_of_emod hdd) (frameW_ne s D.frame hd c.isLt) (sub_ne_zero.mpr ?_)
    (odQ_ne D hv 0 c c.isLt) ?_ ?_
  · exact frame_ne s D.frame hd (by omega) c.isLt (by omega)
  · have := odQ_ne D hv c (c + 1 + e) (by omega); exact_mod_cast this
  · linear_combination -hK

end Kap

/-! ## The covering and the main theorem -/

section Main

variable {p : ℕ} [Fact p.Prime]

lemma odNu_pos (D : ODesign s) (hv : odValid p D) {j t : ℕ} (hj : j < s) (ht : t < j) :
    1 ≤ odNu D j t := by
  have := (hv.2.2.2.2.2.1 j hj (odRow D j t) (od_row_lt D hv.1 hj ht)).2
  unfold odNu; omega

/-- **The coverings of an ordered design** (`lem:ws` in the stored row order, `lem:lexcover` second form). -/
theorem od_cover (D : ODesign s) (hv : odValid p D) (j : Fin s) (σ : Fin s → ZMod p) :
    ∃ o : ℤ, -((odB D p j : ℤ) + odM D p j - 1) ≤ o ∧ o ≤ -(odB D p j : ℤ) ∧
      ∀ c : Fin s, c < j → σ c + (o : ZMod p) * (odK D c j : ZMod p) ∈
        intWin p (-(odBx D p c j : ℤ)) (odBx D p c j) := by
  have hord := hv.1
  have hΓ := hv.2.2.2.2.2.2
  have hjs := j.isLt
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  by_cases hj0 : (j : ℕ) = 0
  · refine ⟨-(odB D p j : ℤ), ?_, le_rfl, fun c hc => absurd hc (by rw [Fin.lt_def]; omega)⟩
    have : odM D p j = 1 := by simp [odM, hj0]
    rw [this]; push_cast; omega
  have hν : ∀ t, t < (j : ℕ) → 1 ≤ odNu D j t := fun t ht => odNu_pos D hv hjs ht
  have hBp : ∀ t, t < (j : ℕ) → odBp D p j t = odBx D p (odRow D j t) j := fun t ht => by
    unfold odBx; rw [od_pos_row D hord hjs ht]
  have hlen : ∀ t < (j : ℕ), 2 * odBp D p j t + 1 ≤ p := by
    intro t ht
    have hr := od_row_lt D hord hjs ht
    rw [hBp t ht]
    have := odBx_le_odB (D := D) (p := p) (odRow D j t) j hr hjs
    have := od_row_lt_p hΓ (odRow D j t) (by omega)
    have := odM_pos (D := D) hp1 (odRow D j t) fun t' ht' => odNu_pos D hv (by omega) ht'
    omega
  set v : ℕ → ℤ := fun t => odK D (odRow D j t) j with hv_def
  have hνf : (fun t => (v t).natAbs) = fun t => odNu D j t := rfl
  obtain ⟨o, ho1, ho2, hgood⟩ := ws_cover p j (by omega) v
    (fun t => -(odBp D p j t : ℤ)) (fun t => 2 * odBp D p j t + 1) hlen
    (fun t ht => hν t ht)
    (by
      have := odNu_le_odBp (D := D) (p := p) (j : ℕ) 0
      change odNu D j 0 ≤ _; omega)
    (fun t ht => by
      rw [hνf, ← odN_eq_wsN]
      change odN D p j t * odNu D j (t + 1) ≤ 2 * odBp D p j (t + 1) + 1
      have h1 : cdiv (odN D p j t * odNu D j (t + 1) - 1) 2 ≤ odBp D p j (t + 1) := by
        simp only [odBp, if_neg (Nat.succ_ne_zero t), Nat.add_sub_cancel]; exact le_max_right _ _
      have h2 := cdiv_mul_ge (odN D p j t * odNu D j (t + 1) - 1) 2 (by norm_num)
      omega)
    (fun t => if ht : odRow D j t < s then σ ⟨odRow D j t, ht⟩ else 0) (-((odB D p j : ℤ) + odM D p j - 1))
  rw [hνf, ← odN_eq_wsN] at ho2
  have hMj : odM D p j = odN D p j ((j : ℕ) - 1) := by simp [odM, hj0]
  have hMj' : (odM D p j : ℤ) = (odN D p j ((j : ℕ) - 1) : ℤ) := by exact_mod_cast hMj
  refine ⟨o, ho1, by omega, fun c hc => ?_⟩
  have hc' : (c : ℕ) < j := hc
  have hpos := od_pos_lt D hord hjs hc'
  have hrow := od_row_pos D hord hjs hc'
  obtain ⟨i, hi, hx⟩ := hgood _ hpos
  simp only [hrow, dif_pos c.isLt, hv_def] at hx
  have hB : odBp D p j (odPos D c j) = odBx D p c j := rfl
  rw [hB] at hi hx
  refine ⟨-(odBx D p c j : ℤ) + i, by omega, by omega, ?_⟩
  rw [hx]

/-- **`thm:MR` for ordered designs** (`thm:LF`, `app:LFdata`: "Theorem MR holds verbatim"). Let `s ≥ 2`,
`p` prime and `D` an ordered design valid at `p` (`odValid`: row orders, places distinct mod `p`, `θ` prime to
`p`, positive superdiagonal prime to `p`, integral nonzero upper triangle, `Γ < p`). For every choice of the
local roots `z_c(θx)` of the frame (`w(z_c(θx)) = θx`, `z_c(0) = a_c`), with the constants `λ_c = θ^c/Q_{0c}`
and the windows of `lem:ws` in the stored row order, selection rules exist, and every selection rule defines
a digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`, quasi-uniform:
`h(P_{[N]}) ≤ (√s p/((p - Γ)/p)) δ(P_{[N]})` for every `N ≥ 2` (`lem:prefix`). -/
theorem od_sound (D : ODesign s) (hs : 2 ≤ s) (hv : odValid p D) (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s D.frame) = C (odTheta D p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.frame c : ℤ) : ZMod p)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (odTheta D p) (odLam D p) zθ (odWin D p) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule (odTheta D p) (odLam D p) zθ (odWin D p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ))
        (((p : ℝ) - odCost D p) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - odCost D p) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (odTheta D p) (odLam D p) zθ rule) zθ)))) := by
  have hΓ := hv.2.2.2.2.2.2
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hνall : ∀ j, j < s → ∀ t, t < j → 1 ≤ odNu D j t := fun j hj t ht => odNu_pos D hv hj ht
  -- `p ≥ 5`: row `0` has `2 B_0 + M_0 ≥ 3`
  have hp5 : 5 ≤ p := by
    have h1 := hνall 1 (by omega) 0 (by omega)
    have h2 := odNu_le_odBp (D := D) (p := p) 1 0
    have h3 : odBx D p 0 1 = odBp D p 1 0 := by
      unfold odBx; rw [show odPos D 0 1 = 0 from by
        have := od_pos_lt D hv.1 (show 1 < s by omega) (show 0 < 1 by omega); omega]
    have h4 := odBx_le_odB (D := D) (p := p) 0 1 (by omega) (by omega)
    have h5 := od_row_lt_p hΓ 0 (by omega)
    have h6 : odM D p 0 = 1 := by simp [odM]
    have hp4 : 4 ≤ p := by omega
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · subst h; exact absurd (Fact.out : Nat.Prime 4) (by decide)
    · exact h
  have hlex : IsLexData p (fun c : Fin s => odB D p c) (fun c => odM D p c) (fun c j => odBx D p c j) := by
    intro c
    dsimp only
    rw [odB_eq_lexB]
    have := od_row_lt_p hΓ c c.isLt
    exact ⟨odM_pos hp1 c (hνall c c.isLt), le_rfl, by omega⟩
  have hcost : lexCost (fun c : Fin s => odB D p c) (fun c => odM D p c) (fun c j => odBx D p c j) < p := by
    rw [od_lexCost]; exact hΓ
  have key := lex_sound p hp5 (by omega) D.frame hv.2.1 (odTheta D p) (odTheta_ne D hv) (odLam D p)
    (odLam_ne D hv) zθ hroot hplace _ _ _ hlex hcost (fun c j => odK D c j)
    (fun c j hcj => od_kap D hv zθ hplace c j hcj)
    (fun c j hcj => by
      have := odNu_le_odBp (D := D) (p := p) j (odPos D c j)
      unfold odNu at this
      rw [od_row_pos D hv.1 j.isLt hcj] at this
      exact this)
    (fun j σ => od_cover D hv j σ)
  rw [od_lexCost] at key
  exact key

/-- **A valid ordered design gives a sequence** (`thm:LF`(a), existential form): a quasi-uniform digital
`(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem od_seq (D : ODesign s) (hs : 2 ≤ s) (hv : odValid p D) :
    ∃ C : Gen s (ZMod p), IsSeq0 (zcode p) C ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) C) (((p : ℝ) - odCost D p) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) C)) ≤
          Real.sqrt s * p / (((p : ℝ) - odCost D p) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) C))) := by
  obtain ⟨zθ, hroot, hplace⟩ := frame_roots_exist p s D.frame hv.2.1 (odTheta D p)
  obtain ⟨⟨rule, hrule⟩, hall⟩ := od_sound D hs hv zθ hroot hplace
  exact ⟨_, hall rule hrule⟩

end Main

end GeoSeq
