/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Law
public import GeoSeq.T0
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S10: `prop:N1` (no lattice law) and the box bijection of a net prefix

* `box_existsUnique`: if the prefix `P_m` is a `(0,m,s)`-net, then for EVERY composition `d` of `m`
  and every digit pattern there is exactly one index vector `V ∈ R^m` with these first `d_c` digits
  (generalises `cell_existsUnique`, which is the composition `(K, …, K)`).
* `exists_digitCode`: every finite commutative ring has a digit code.
* `expand_zero_cells`: at level `K`, a vector whose cells vanish in coordinate `0` is the combination
  `∑_n y_{1,n}(V) U_n` of the unit cell vectors `U_n` of coordinate `1` (any digit functional).
* `finest_zero`: a finest-digit law entry `(c, 1)` kills the unit cell vectors `U_n`, `n < K - 1`.
* **`N1_general`**: for ANY digital sequence in dimension two whose coordinate `0` is lower triangular
  with nonzero diagonal and whose prefixes `P_{2K}`, `P_{2K+2}` are nets, the three finest-digit
  conditions of `prop:N1` cannot hold together (`K ≥ 2`).
* **`N1`** (`prop:N1`): the scrambled Faure frame `(L_0, L_1 P_1)` over any finite field.

The formal proof is elementary and differs from the residue argument of the paper: it evaluates the
three laws on the index vectors `z^K` and `z^{K+1}` (whose cells vanish in coordinate `0`, since
`C_0` is lower triangular). It uses nothing about coordinate `1` beyond `t = 0`.
-/

namespace GeoSeq

open Finset

section Box

variable {R : Type*} [CommRing R] {s q : ℕ} [NeZero q]

/-- If the prefix `P_m` is a `(0,m,s)`-net, every pattern of first digits, for every composition `d`
of `m`, is attained by exactly one index vector `V ∈ R^m`. -/
lemma box_existsUnique (D : DigitCode R q) (C : Gen s R) (m : ℕ)
    (hnet : BlockNet0 D C m 0) (d : Fin s → ℕ) (hd : ∑ c, d c = m) (T : Fin s → ℕ → R) :
    ∃! V : Fin m → R, ∀ c, ∀ n < d c, vecDigit C V c n = T c n := by
  set a : Fin s → ℕ := fun c => Z3Net.Proofs.digSum q (d c) (fun n => (D.enc (T c n) : ℕ)) with hadef
  have ha : ∀ c, a c < q ^ d c := fun c =>
    Z3Net.Proofs.digSum_lt q (d c) _ (fun _ => (D.enc _).isLt)
  have h := hnet d hd a ha
  rw [existsUnique_block D m 0] at h
  refine (existsUnique_congr fun V => ?_).1 h
  refine forall_congr' fun c => ?_
  have hfun : (fun n : Fin (d c) => (D.enc (seqDigit D C (blockIdx D m 0 V) c n) : ℕ)) =
      fun n : Fin (d c) => (D.enc (vecDigit C V c n) : ℕ) := by
    funext n
    rw [seqDigit_block, seqDigit_zero, add_zero]
    rfl
  show Z3Net.Proofs.digSum q (d c) _ = a c ↔ _
  rw [hfun, digSum_enc_eq_iff D (d c) (a c) (ha c)]
  constructor
  · intro h n hn
    rw [h ⟨n, hn⟩]
    exact digOf_digSum D (d c) (fun n => T c n) ⟨n, hn⟩
  · intro h n
    rw [h n n.isLt]
    exact (digOf_digSum D (d c) (fun n => T c n) n).symm

end Box

/-- Every finite commutative ring has a digit code (`enc 0 = 0`). -/
lemma exists_digitCode (R : Type*) [CommRing R] [Fintype R] :
    ∃ D : DigitCode R (Fintype.card R), True := by
  have hpos : 0 < Fintype.card R := Fintype.card_pos
  let e0 : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let e : R ≃ Fin (Fintype.card R) := e0.trans (Equiv.swap (e0 0) ⟨0, hpos⟩)
  refine ⟨⟨e, ?_⟩, trivial⟩
  simp [e]

section Vec

variable {R : Type*} [CommRing R] {s : ℕ}

lemma vecDigit_add {m : ℕ} (C : Gen s R) (V W : Fin m → R) (c : Fin s) (n : ℕ) :
    vecDigit C (V + W) c n = vecDigit C V c n + vecDigit C W c n := by
  simp [vecDigit, mul_add, Finset.sum_add_distrib]

lemma vecDigit_smul {m : ℕ} (C : Gen s R) (a : R) (V : Fin m → R) (c : Fin s) (n : ℕ) :
    vecDigit C (a • V) c n = a * vecDigit C V c n := by
  simp [vecDigit, Finset.mul_sum, mul_left_comm]

lemma vecDigit_sum {m : ℕ} {ι : Type*} (C : Gen s R) (S : Finset ι) (V : ι → Fin m → R)
    (c : Fin s) (n : ℕ) : vecDigit C (∑ i ∈ S, V i) c n = ∑ i ∈ S, vecDigit C (V i) c n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [vecDigit]
  | insert a S ha ih => rw [Finset.sum_insert ha, vecDigit_add, ih, Finset.sum_insert ha]

lemma vecDigit_zero {m : ℕ} (C : Gen s R) (c : Fin s) (n : ℕ) :
    vecDigit C (0 : Fin m → R) c n = 0 := by
  simp [vecDigit]

lemma vecDigit_single {m : ℕ} (C : Gen s R) (j : Fin m) (c : Fin s) (n : ℕ) :
    vecDigit C (Pi.single j 1) c n = C c n j := by
  simp [vecDigit, Pi.single_apply]

end Vec

section N1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-- The unit cell vector of coordinate `1`, digit `n`, at level `K` (cells `e_{1,n}`), chosen. -/
noncomputable def unitCell (D : DigitCode F q) (C : Gen 2 F) (K : ℕ)
    (hnet : BlockNet0 D C (2 * K) 0) (n : ℕ) : Fin (2 * K) → F :=
  (cell_existsUnique D C K hnet (fun c j => if c = 1 ∧ j = n then 1 else 0)).exists.choose

lemma unitCell_spec (D : DigitCode F q) (C : Gen 2 F) (K : ℕ) (hnet : BlockNet0 D C (2 * K) 0)
    (n : ℕ) (c : Fin 2) (j : ℕ) (hj : j < K) :
    vecDigit C (unitCell D C K hnet n) c j = if c = 1 ∧ j = n then 1 else 0 :=
  (cell_existsUnique D C K hnet (fun c j => if c = 1 ∧ j = n then 1 else 0)).exists.choose_spec c j hj

/-- **Expansion**: if the cells of `V` vanish in coordinate `0`, then every digit of `V` is
`∑_{n<K} y_{1,n}(V) · (digit of U_n)`. -/
lemma expand_zero_cells (D : DigitCode F q) (C : Gen 2 F) (K : ℕ) (hnet : BlockNet0 D C (2 * K) 0)
    (V : Fin (2 * K) → F) (hV : ∀ n < K, vecDigit C V 0 n = 0) (c : Fin 2) (i : ℕ) :
    vecDigit C V c i =
      ∑ n ∈ range K, vecDigit C V 1 n * vecDigit C (unitCell D C K hnet n) c i := by
  set W : Fin (2 * K) → F := ∑ n ∈ range K, vecDigit C V 1 n • unitCell D C K hnet n with hW
  have hcells : ∀ c₁ : Fin 2, ∀ j < K, vecDigit C (V - W) c₁ j = 0 := by
    intro c₁ j hj
    have hsub : V - W = V + (-1 : F) • W := by simp [sub_eq_add_neg]
    rw [hsub, vecDigit_add, vecDigit_smul, hW, vecDigit_sum]
    simp_rw [vecDigit_smul, unitCell_spec D C K hnet _ c₁ j hj]
    fin_cases c₁
    · simp [hV j hj]
    · simp only [Fin.mk_one, true_and]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.2 hj) h
  have h0 : V - W = 0 := by
    obtain ⟨U, _, hU⟩ := cell_existsUnique D C K hnet (fun _ _ => (0 : F))
    exact (hU _ hcells).trans (hU 0 fun c₁ j _ => vecDigit_zero C c₁ j).symm
  have hVW : V = W := sub_eq_zero.1 h0
  conv_lhs => rw [hVW, hW]
  rw [vecDigit_sum]
  simp_rw [vecDigit_smul]

/-- A finest-digit law entry `(c, 1)` at level `K` kills the unit cell vectors `U_n`, `n + 1 < K`. -/
lemma finest_zero (D : DigitCode F q) (C : Gen 2 F) (K : ℕ) (hnet : BlockNet0 D C (2 * K) 0)
    (c : Fin 2) (hfin : LawFinest C K c 1) (n : ℕ) (hn : n + 1 < K) :
    vecDigit C (unitCell D C K hnet n) c K = 0 := by
  obtain ⟨d, hd⟩ := hfin
  -- the carry vector of length `l` is `∑_{K-l ≤ j < K} U_j`
  have hX : ∀ l, 1 ≤ l → l ≤ K →
      vecDigit C (∑ j ∈ Finset.Ico (K - l) K, unitCell D C K hnet j) c (K + 0) = d := by
    intro l hl hlK
    refine (hd l hl hlK).2 _ fun c₁ j hj => ?_
    rw [vecDigit_sum]
    simp_rw [unitCell_spec D C K hnet _ c₁ j hj]
    unfold carryPat
    by_cases h1 : c₁ = 1
    · subst h1
      by_cases hjr : K - l ≤ j
      · rw [Finset.sum_eq_single j]
        · simp [hjr, hj]
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_Ico.2 ⟨hjr, hj⟩) h
      · rw [Finset.sum_eq_zero]
        · simp [hjr]
        · intro b hb
          have : b ≠ j := by intro h; subst h; exact hjr (Finset.mem_Ico.1 hb).1
          simp [Ne.symm this]
    · simp [h1]
  have hl1 := hX (K - n) (by omega) (by omega)
  have hl2 := hX (K - n - 1) (by omega) (by omega)
  have hsplit : Finset.Ico (K - (K - n)) K = insert n (Finset.Ico (K - (K - n - 1)) K) := by
    have e1 : K - (K - n) = n := by omega
    have e2 : K - (K - n - 1) = n + 1 := by omega
    rw [e1, e2]
    exact (Finset.insert_Ico_add_one_left_eq_Ico (by omega)).symm
  rw [hsplit, Finset.sum_insert (by simp; omega), vecDigit_add] at hl1
  simp only [add_zero] at hl1 hl2
  rw [hl2] at hl1
  simpa using hl1

/-- Coordinate `0` lower triangular: the cells (digits `< K`) of `z^K` and `z^{K+1}` vanish. -/
lemma cells_single_zero (C : Gen 2 F) (htri : ∀ n k, n < k → C 0 n k = 0) {m : ℕ} (j : Fin m)
    (K : ℕ) (hj : K ≤ (j : ℕ)) : ∀ n < K, vecDigit C (Pi.single j 1) 0 n = 0 := by
  intro n hn
  rw [vecDigit_single]
  exact htri n j (by omega)

/-- **`prop:N1`, general form**: let `C` be a two-dimensional digital sequence over a finite field
whose coordinate `0` is lower triangular with nonzero diagonal, and whose prefixes `P_{2K}` and
`P_{2K+2}` are nets (`K ≥ 2`). Then it is impossible that the cross law of coordinate `0` is
finest-digit at both levels `K` and `K+1` and the own law of coordinate `1` is finest-digit at
level `K`. -/
theorem N1_general (D : DigitCode F q) (C : Gen 2 F) (K : ℕ) (hK : 2 ≤ K)
    (hnet : BlockNet0 D C (2 * K) 0) (hnet' : BlockNet0 D C (2 * (K + 1)) 0)
    (htri : ∀ n k, n < k → C 0 n k = 0) (hdiag : ∀ n, C 0 n n ≠ 0) :
    ¬ (LawFinest C K 0 1 ∧ LawFinest C (K + 1) 0 1 ∧ LawFinest C K 1 1) := by
  rintro ⟨h0K, h0K1, h1K⟩
  -- level `K`: the index vectors `z^K`, `z^{K+1}` (`K + 1 < 2K`)
  have expK := expand_zero_cells D C K hnet
  set U := unitCell D C K hnet with hUdef
  have hsum : ∀ (c : Fin 2) (j : Fin (2 * K)), K ≤ (j : ℕ) →
      (∀ n, n + 1 < K → vecDigit C (U n) c K = 0) →
      C c K j = C 1 (K - 1) j * vecDigit C (U (K - 1)) c K := by
    intro c j hj hz
    have h := expK (Pi.single j 1) (cells_single_zero C htri j K hj) c K
    rw [vecDigit_single] at h
    rw [h, Finset.sum_eq_single (K - 1)]
    · rw [vecDigit_single]
    · intro b hb hne
      rw [hz b (by have := Finset.mem_range.1 hb; omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have z0 : ∀ n, n + 1 < K → vecDigit C (U n) 0 K = 0 := fun n hn =>
    finest_zero D C K hnet 0 h0K n hn
  have z1 : ∀ n, n + 1 < K → vecDigit C (U n) 1 K = 0 := fun n hn =>
    finest_zero D C K hnet 1 h1K n hn
  have iK := hsum 0 ⟨K, by omega⟩ le_rfl z0
  have iK1 := hsum 0 ⟨K + 1, by omega⟩ (by simp) z0
  have jK1 := hsum 1 ⟨K + 1, by omega⟩ (by simp) z1
  simp only at iK iK1 jK1
  have hr0 : vecDigit C (U (K - 1)) 0 K ≠ 0 := by
    intro h; rw [h, mul_zero] at iK; exact hdiag K iK
  have hc : C 1 (K - 1) (K + 1) = 0 := by
    rw [htri K (K + 1) (by omega)] at iK1
    exact (mul_eq_zero.1 iK1.symm).resolve_right hr0
  have hc' : C 1 K (K + 1) = 0 := by rw [jK1, hc, zero_mul]
  -- level `K + 1`: the index vector `z^{K+1}` (`K + 1 < 2K + 2`)
  have expK1 := expand_zero_cells D C (K + 1) hnet'
  have h := expK1 (Pi.single ⟨K + 1, by omega⟩ 1)
    (cells_single_zero C htri _ (K + 1) le_rfl) 0 (K + 1)
  rw [vecDigit_single] at h
  rw [Finset.sum_eq_single K] at h
  · rw [vecDigit_single] at h
    simp only at h
    rw [hc', zero_mul] at h
    exact hdiag (K + 1) h
  · intro b hb hne
    rw [finest_zero D C (K + 1) hnet' 0 h0K1 b (by have := Finset.mem_range.1 hb; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **`prop:N1`** (no lattice law): for the Faure frame `a_0 = 0`, `a_1 = 1`, `K ≥ 2` and ANY scramble
`(L_0, L_1)` (lower triangular, nonzero diagonal) over any finite field, it is impossible that the cross
law of coordinate `0` is finest-digit at both levels `K` and `K+1` and the own law of coordinate `1` is
finest-digit at level `K`. -/
theorem N1 (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (K : ℕ) (hK : 2 ≤ K) :
    ¬ (LawFinest (scrGen ![0, 1] L) K 0 1 ∧ LawFinest (scrGen ![0, 1] L) (K + 1) 0 1 ∧
      LawFinest (scrGen ![0, 1] L) K 1 1) := by
  obtain ⟨D, -⟩ := exists_digitCode F
  have hinj : Function.Injective (![0, 1] : Fin 2 → F) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hseq := t0 D ![0, 1] hinj L hL
  have htri : ∀ n k, n < k → scrGen ![0, 1] L 0 n k = 0 := by
    intro n k hnk
    simp only [scrGen, pas, Matrix.cons_val_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i < k := by have := Finset.mem_range.1 hi; omega
    simp [zero_pow (Nat.sub_ne_zero_of_lt this)]
  have hdiag : ∀ n, scrGen ![0, 1] L 0 n n ≠ 0 := by
    intro n
    simp only [scrGen, pas, Matrix.cons_val_zero]
    rw [Finset.sum_eq_single n]
    · simpa using hL 0 n
    · intro b hb hne
      have : b < n := by have := Finset.mem_range.1 hb; omega
      simp [zero_pow (Nat.sub_ne_zero_of_lt this)]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  exact N1_general D _ K hK (hseq _ 0) (hseq _ 0) htri hdiag

end N1

end GeoSeq
