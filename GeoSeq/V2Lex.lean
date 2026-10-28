/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2Defs
public import GeoSeq.V1Aux
public import GeoSeq.Window

@[expose] public section

/-!
# GeoSeq stage V2: ordered windows (`def:lex`, `lem:lex`, `rem:lexexact`, `lem:lexcover`)

* `lex_bound`, **`lex_cost`** (`lem:lex`): for ordered windows `p LB(W) ≥ min_c (p - A_c - M_c - B_c)`.
* **`lex_exact`**, **`lex_eq`** (`rem:lexexact`): the bound is exact, `LB(W) = (p - max_c (A_c+M_c+B_c))/p`
  (`IsGreatest`), in particular `LB(W) = (p - Γ)/p` for `A_c = B_c` (`lex_eq_cost`).
* **`lexcover_iff`**, **`lexcover_lattice`**, `lexcover_zero` (`lem:lexcover`).
-/

namespace GeoSeq

open Finset

section LexWin

variable {s : ℕ}

lemma lexWin_low (p : ℕ) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) {c c' : Fin s} (h : c' < c) :
    lexWin p A M Bx c c' = Set.univ := by
  simp [lexWin, h]

lemma lexWin_up (p : ℕ) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) {c c' : Fin s} (h : c < c') :
    lexWin p A M Bx c c' = intWin p (-(Bx c c' : ℤ)) (Bx c c') := by
  simp [lexWin, h, not_lt_of_gt h]

lemma lexWin_own (p : ℕ) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (c : Fin s) :
    lexWin p A M Bx c c = intWin p (-((A c : ℤ) + M c - 1)) (-(A c : ℤ)) := by
  simp [lexWin]

lemma lexB_eq (Bx : Fin s → Fin s → ℕ) (c : Fin s) :
    (∑ c' ∈ univ.erase c, (if c < c' then (Bx c c' : ℤ) else 0)) = lexB Bx c := by
  rw [lexB, ← Finset.sum_filter]
  push_cast
  congr 1
  ext c'
  simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
  exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩

/-- Row `c` of a step whose first moving coordinate is `c` (with `e_c = 1`): every `σ ∈ S_c(e)` has
`p f_1(1, σ) ≥ p - A_c - M_c - B_c` (the proof of `lem:lex`). -/
lemma lex_row (p : ℕ) [NeZero p] (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p A M Bx)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (c : Fin s) (hc : e c = 1)
    (hlt : ∀ c', c' < c → e c' = 0) (σ : ZMod p) (hσ : σ ∈ sumsetS (lexWin p A M Bx) e c) :
    (p : ℤ) - A c - M c - lexB Bx c ≤ gapNum1 p 1 σ := by
  obtain ⟨x, hx, rfl⟩ := hσ
  obtain ⟨hM, hBA, hp⟩ := hd c
  have hz : ∀ c', ∃ z : ℤ, (e c' : ZMod p) * x c' = ((e c' * z : ℤ) : ZMod p) ∧
      (c' = c → -((A c : ℤ) + M c - 1) ≤ z ∧ z ≤ -(A c : ℤ)) ∧
      (c' ≠ c → |e c' * z| ≤ (if c < c' then (Bx c c' : ℤ) else 0)) := by
    intro c'
    by_cases he0 : e c' = 0
    · refine ⟨0, by simp [he0], fun h => ?_, fun _ => ?_⟩
      · subst h; rw [hc] at he0; exact absurd he0 one_ne_zero
      · simp only [he0, zero_mul, abs_zero]; split_ifs <;> simp
    · have hmem := hx c' he0
      by_cases hcc : c' = c
      · subst hcc
        rw [lexWin_own] at hmem
        obtain ⟨z, h1, h2, hz⟩ := hmem
        refine ⟨z, by rw [← hz]; push_cast; ring, fun _ => ⟨h1, h2⟩, fun h => absurd rfl h⟩
      · have hgt : c < c' := by
          rcases lt_trichotomy c' c with h | h | h
          · exact absurd (hlt c' h) he0
          · exact absurd h hcc
          · exact h
        rw [lexWin_up p A M Bx hgt] at hmem
        obtain ⟨z, h1, h2, hz⟩ := hmem
        refine ⟨z, by rw [← hz]; push_cast; ring, fun h => absurd h hcc, fun _ => ?_⟩
        rw [if_pos hgt, abs_mul]
        have : |e c'| ≤ 1 := abs_le.mpr ⟨(he c').1, (he c').2⟩
        have hz' : |z| ≤ (Bx c c' : ℤ) := abs_le.mpr ⟨h1, h2⟩
        nlinarith [abs_nonneg z, abs_nonneg (e c')]
  choose z hz1 hz2 hz3 using hz
  have hsum : (∑ c', (e c' : ZMod p) * x c') = ((∑ c', e c' * z c' : ℤ) : ZMod p) := by
    push_cast
    exact Finset.sum_congr rfl fun c' _ => by rw [hz1 c']; push_cast; ring
  rw [hsum]
  have hsplit : (∑ c', e c' * z c') = z c + ∑ c' ∈ univ.erase c, e c' * z c' := by
    rw [← Finset.add_sum_erase _ _ (mem_univ c), hc, one_mul]
  have hR : |∑ c' ∈ univ.erase c, e c' * z c'| ≤ lexB Bx c := by
    rw [← lexB_eq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c' hc' => ?_)
    exact hz3 c' (Finset.ne_of_mem_erase hc')
  have hzc := hz2 c rfl
  set R := ∑ c' ∈ univ.erase c, e c' * z c'
  have hR' := abs_le.mp hR
  rw [hsplit, f1_int_nonpos p _ (by omega) (by omega)]
  omega

/-- The first moving coordinate of a step: some row `c` has `p f_1(e_c, σ_c) ≥ p - A_c - M_c - B_c`. -/
lemma lex_some_row (p : ℕ) [NeZero p] (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0)
    (σ : Fin s → ZMod p) (hσ : ∀ c, σ c ∈ sumsetS (lexWin p A M Bx) e c) :
    ∃ c, (p : ℤ) - A c - M c - lexB Bx c ≤ gapNum1 p (e c) (σ c) := by
  classical
  have hS : (univ.filter fun c => e c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := hne; exact ⟨c, by simp [hc]⟩
  set c := (univ.filter fun c => e c ≠ 0).min' hS
  have hc : e c ≠ 0 := by have := Finset.min'_mem _ hS; simpa using this
  have hlt : ∀ c', c' < c → e c' = 0 := by
    intro c' h
    by_contra hne'
    have hm' : c' ∈ univ.filter (fun c => e c ≠ 0) := by simp [hne']
    have := Finset.min'_le _ c' hm'
    exact absurd h (not_lt_of_ge this)
  refine ⟨c, ?_⟩
  rcases (show e c = 1 ∨ e c = -1 by have := he c; omega) with h1 | h1
  · rw [h1]; exact lex_row p A M Bx hd e he c h1 hlt (σ c) (hσ c)
  · have hrow := lex_row p A M Bx hd (-e) (fun c => by have := he c; show -1 ≤ -e c ∧ -e c ≤ 1; omega)
      c (by simp [h1]) (fun c' h => by simp [hlt c' h]) (-σ c)
      ((sumsetS_neg _ e c (σ c)).mpr (hσ c))
    have : gapNum1 p 1 (-σ c) = gapNum1 p (e c) (σ c) := by
      rw [h1, ← gapNum1_neg p (-1) (σ c)]; simp
    rwa [this] at hrow

/-- **`lem:lex`** (first moving coordinate): for ordered windows (`def:lex`), every
`L ≤ min_c (p - A_c - M_c - B_c)` gives `L/p ≤ LB(W)`, i.e. `p LB(W) ≥ min_c (p - A_c - M_c - B_c)`. -/
theorem lex_bound (p : ℕ) [NeZero p] (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) (L : ℝ) (hL : ∀ c, L ≤ (p : ℝ) - A c - M c - lexB Bx c) :
    WinLB p (lexWin p A M Bx) (L / p) := by
  intro e he hne σ hσ
  obtain ⟨c, hc⟩ := lex_some_row p A M Bx hd e he hne σ hσ
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hcR : (p : ℝ) - A c - M c - lexB Bx c ≤ gapNum1 p (e c) (σ c) := by exact_mod_cast hc
  have h0 : (0 : ℝ) ≤ (gapNum1 p (e c) (σ c) : ℝ) / p := by positivity
  calc L / p ≤ (gapNum1 p (e c) (σ c) : ℝ) / p :=
        div_le_div_of_nonneg_right ((hL c).trans hcR) hp.le
    _ ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2) := by
        rw [Real.le_sqrt h0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        exact Finset.single_le_sum (f := fun c => ((gapNum1 p (e c) (σ c) : ℝ) / p) ^ 2)
          (fun _ _ => sq_nonneg _) (mem_univ c)

/-- **`lem:lex`** with the cost: `LB(W) ≥ (p - max_c (A_c + M_c + B_c))/p`. -/
theorem lex_cost (p : ℕ) [NeZero p] (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) :
    WinLB p (lexWin p A M Bx) (((p : ℝ) - lexCost A M Bx) / p) := by
  refine lex_bound p A M Bx hd _ fun c => ?_
  have : A c + M c + lexB Bx c ≤ lexCost A M Bx :=
    Finset.le_sup (f := fun c => A c + M c + lexB Bx c) (mem_univ c)
  have : (A c : ℝ) + M c + lexB Bx c ≤ lexCost A M Bx := by exact_mod_cast this
  linarith

/-- If `e_c = 1`, the window `W_{r←c}` is full and all windows of row `r` are nonempty, then
`S_r(e) = 𝔽_p` (a full window in a moving column). -/
lemma sumsetS_full {p : ℕ} (W : Fin s → Fin s → Set (ZMod p)) (e : Fin s → ℤ) (r c : Fin s)
    (hec : e c = 1) (hfull : W r c = Set.univ) (hne : ∀ c', (W r c').Nonempty) (σ : ZMod p) :
    σ ∈ sumsetS W e r := by
  classical
  choose y hy using hne
  set v := σ - ∑ c' ∈ univ.erase c, (e c' : ZMod p) * y c'
  refine ⟨Function.update y c v, fun c' _ => ?_, ?_⟩
  · by_cases h : c' = c
    · subst h; rw [hfull]; trivial
    · rw [Function.update_of_ne h]; exact hy c'
  · rw [← Finset.add_sum_erase _ _ (mem_univ c), Function.update_self, hec]
    have hs : ∑ c' ∈ univ.erase c, (e c' : ZMod p) * Function.update y c v c' =
        ∑ c' ∈ univ.erase c, (e c' : ZMod p) * y c' :=
      Finset.sum_congr rfl fun c' hc' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hc')]
    rw [hs]; simp only [v]; push_cast; ring

lemma gapNum1_one_one (p : ℕ) [NeZero p] (hp : 2 ≤ p) : gapNum1 p 1 (1 : ZMod p) = 0 := by
  have : Fact (1 < p) := ⟨by omega⟩
  rw [f1_one_val, if_neg one_ne_zero, ZMod.val_one]

lemma gapNum1_zero_zero (p : ℕ) [NeZero p] : gapNum1 p 0 (0 : ZMod p) = 0 := by
  rw [f1_zero_val]; simp

/-- **`rem:lexexact`** (the bound is exact), one row: for ordered windows, every `LB ≤ LB(W)` has
`LB ≤ (p - A_c - M_c - B_c)/p` for every row `c` (step `e = 1_c + ∑_{c'>c} 1_{c'}`). -/
theorem lex_exact_row (p : ℕ) [NeZero p] (hp : 2 ≤ p) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) (LB : ℝ) (hLB : WinLB p (lexWin p A M Bx) LB) (c : Fin s) :
    LB ≤ ((p : ℝ) - A c - M c - lexB Bx c) / p := by
  classical
  obtain ⟨hM, hBA, hpc⟩ := hd c
  set e : Fin s → ℤ := fun r => if c ≤ r then 1 else 0 with he_def
  set T : ℤ := -((A c : ℤ) + M c - 1 + lexB Bx c)
  set σ : Fin s → ZMod p := fun r => if r < c then 0 else if r = c then (T : ZMod p) else 1
  have hne : ∀ r c', (lexWin p A M Bx r c').Nonempty := by
    intro r c'
    rcases lt_trichotomy c' r with h | h | h
    · rw [lexWin_low p A M Bx h]; exact Set.univ_nonempty
    · subst h; rw [lexWin_own]; exact ⟨_, -(A c' : ℤ), by have := (hd c').1; omega, le_rfl, rfl⟩
    · rw [lexWin_up p A M Bx h]; exact ⟨_, 0, by omega, by omega, rfl⟩
  have hmem : ∀ r, σ r ∈ sumsetS (lexWin p A M Bx) e r := by
    intro r
    rcases lt_trichotomy r c with h | h | h
    · refine ⟨0, fun c' hc' => ?_, by simp [σ, h]⟩
      have : c ≤ c' := by by_contra hh; exact hc' (by simp [he_def, hh])
      rw [lexWin_up p A M Bx (lt_of_lt_of_le h this)]; exact ⟨0, by omega, by omega, by simp⟩
    · subst h
      refine ⟨fun c' => if c' = r then ((-((A r : ℤ) + M r - 1) : ℤ) : ZMod p)
        else if r < c' then ((-(Bx r c' : ℤ) : ℤ) : ZMod p) else 0, fun c' hc' => ?_, ?_⟩
      · have hle : r ≤ c' := by by_contra hh; exact hc' (by simp [he_def, hh])
        dsimp only
        rcases eq_or_lt_of_le hle with h' | h'
        · subst h'; simp only [if_true]; rw [lexWin_own]; exact ⟨_, le_rfl, by omega, rfl⟩
        · rw [if_neg (ne_of_gt h'), if_pos h', lexWin_up p A M Bx h']
          exact ⟨_, le_rfl, by omega, rfl⟩
      · simp only [σ, lt_irrefl, if_false, if_true]
        rw [← Finset.add_sum_erase _ _ (mem_univ r)]
        simp only [he_def, le_refl, if_true, Int.cast_one, one_mul]
        have : (∑ c' ∈ univ.erase r, ((if r ≤ c' then (1 : ℤ) else 0 : ℤ) : ZMod p) *
            (if c' = r then ((-((A r : ℤ) + M r - 1) : ℤ) : ZMod p)
              else if r < c' then ((-(Bx r c' : ℤ) : ℤ) : ZMod p) else 0)) =
            ((-(∑ c' ∈ univ.erase r, if r < c' then (Bx r c' : ℤ) else 0) : ℤ) : ZMod p) := by
          push_cast
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun c' hc' => ?_
          have hne' := Finset.ne_of_mem_erase hc'
          rw [if_neg hne']
          by_cases hrc : r < c'
          · simp [hrc, le_of_lt hrc]
          · have : ¬ r ≤ c' := fun hh => hrc (lt_of_le_of_ne hh (Ne.symm hne'))
            simp [hrc, this]
        rw [this, lexB_eq]
        simp only [T]; push_cast; ring
    · have hσr : σ r = 1 := by simp [σ, not_lt_of_gt h, ne_of_gt h]
      rw [hσr]
      exact sumsetS_full _ e r c (by simp [he_def]) (lexWin_low p A M Bx h) (hne r) 1
  have hstep := hLB e (fun r => by simp only [he_def]; split_ifs <;> norm_num) ⟨c, by simp [he_def]⟩ σ hmem
  have hterm : ∀ r, r ≠ c → ((gapNum1 p (e r) (σ r) : ℝ) / p) ^ 2 = 0 := by
    intro r hr
    rcases lt_or_gt_of_ne hr with h | h
    · have h1 : e r = 0 := by simp [he_def, not_le_of_gt h]
      have h2 : σ r = 0 := by simp [σ, h]
      rw [h1, h2, gapNum1_zero_zero]; simp
    · have h1 : e r = 1 := by simp [he_def, le_of_lt h]
      have h2 : σ r = 1 := by simp [σ, not_lt_of_gt h, ne_of_gt h]
      rw [h1, h2, gapNum1_one_one p hp]; simp
  rw [Finset.sum_eq_single c (fun r _ hr => hterm r hr) (fun h => absurd (mem_univ c) h)] at hstep
  have hec : e c = 1 := by simp [he_def]
  have hσc : σ c = (T : ZMod p) := by simp [σ]
  rw [hec, hσc] at hstep
  have hg : (gapNum1 p 1 (T : ZMod p) : ℝ) = (p : ℝ) - 1 + T := by
    have := f1_int_nonpos p T (by simp only [T]; omega) (by simp only [T]; omega)
    have h2 : ((gapNum1 p 1 (T : ZMod p) : ℤ) : ℝ) = (((p : ℤ) - 1 + T : ℤ) : ℝ) := by rw [this]
    push_cast at h2; exact h2
  have hnn : (0 : ℝ) ≤ ((p : ℝ) - 1 + T) / p := by
    apply div_nonneg _ (by positivity)
    have : (0 : ℤ) ≤ (p : ℤ) - 1 + T := by simp only [T]; omega
    exact_mod_cast this
  rw [hg, Real.sqrt_sq hnn] at hstep
  refine hstep.trans (le_of_eq ?_)
  simp only [T]; push_cast; ring


/-- **`rem:lexexact`**: every `LB ≤ LB(W)` has `LB ≤ (p - max_c (A_c + M_c + B_c))/p`. -/
theorem lex_exact (p : ℕ) [NeZero p] (hp : 2 ≤ p) (hs : 0 < s) (A M : Fin s → ℕ)
    (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p A M Bx) (LB : ℝ)
    (hLB : WinLB p (lexWin p A M Bx) LB) : LB ≤ ((p : ℝ) - lexCost A M Bx) / p := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin s)) ⟨⟨0, hs⟩, mem_univ _⟩
    (fun c => A c + M c + lexB Bx c)
  have := lex_exact_row p hp A M Bx hd LB hLB c
  rw [lexCost, hc]; push_cast
  convert this using 2; ring

/-- **`lem:lex` + `rem:lexexact`** (the bound is exact): for ordered windows the window bound is
`LB(W) = (p - max_c (A_c + M_c + B_c))/p`, i.e. this number is the greatest `LB` with `LB ≤ LB(W)`. -/
theorem lex_eq (p : ℕ) [NeZero p] (hp : 2 ≤ p) (hs : 0 < s) (A M : Fin s → ℕ)
    (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p A M Bx) :
    IsGreatest {LB : ℝ | WinLB p (lexWin p A M Bx) LB} (((p : ℝ) - lexCost A M Bx) / p) :=
  ⟨lex_cost p A M Bx hd, fun LB hLB => lex_exact p hp hs A M Bx hd LB hLB⟩

/-- **`rem:lexexact`** for `A_c = B_c`: `LB(W) = (p - Γ)/p` with the cost `Γ = max_c (2B_c + M_c)`. -/
theorem lex_eq_cost (p : ℕ) [NeZero p] (hp : 2 ≤ p) (hs : 0 < s) (M : Fin s → ℕ)
    (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p (lexB Bx) M Bx) :
    IsGreatest {LB : ℝ | WinLB p (lexWin p (lexB Bx) M Bx) LB}
      (((p : ℝ) - (univ.sup fun c => 2 * lexB Bx c + M c)) / p) := by
  have e : lexCost (lexB Bx) M Bx = univ.sup fun c => 2 * lexB Bx c + M c := by
    unfold lexCost; congr 1; funext c; ring
  rw [← e]; exact lex_eq p hp hs _ M Bx hd

end LexWin

section Cover

variable {s : ℕ}

/-- **`lem:lexcover`** (coverings for ordered windows, second form): if the lower crosses of column `j`
are full, condition (ii) of `prop:steer` for column `j` holds iff for every `σ` some `o ∈ Wo^{(j)}` has
`σ_c + o κ_{c←j} ∈ W_{c←j}` for all `c < j` (only the entries `σ_c`, `c < j`, are read). -/
theorem lexcover_iff {F : Type*} [Field F] (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (W : Fin s → Fin s → Set F) (j : Fin s) (hlow : ∀ c, j < c → W c j = Set.univ) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin W j) ↔
      ∀ σ : Fin s → F, ∃ o ∈ W j j, ∀ c, c < j → σ c + o * kapL θ lamv zθ c j ∈ W c j := by
  constructor
  · intro hL σ
    obtain ⟨t, ht⟩ := hL (fun c => if c = j then 0 else σ c)
    refine ⟨t, ?_, fun c hc => ?_⟩
    · have := ht j; simpa [stAlpha] using this
    · have := ht c; simpa [stAlpha, ne_of_lt hc] using this
  · intro hσ β
    obtain ⟨o, ho, hc⟩ := hσ (fun c => β c - β j * kapL θ lamv zθ c j)
    refine ⟨o - β j, fun c => ?_⟩
    rcases lt_trichotomy c j with h | h | h
    · have := hc c h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, stAlpha, if_neg (ne_of_lt h)]
      convert this using 1; ring
    · subst h; simpa [stAlpha] using ho
    · rw [hlow c h]; trivial

/-- **`lem:lexcover`**, column `0`: the own window of ordered windows is nonempty (`M_0 ≥ 1`), so
column `0` satisfies (ii) (all its crosses are lower, hence full). -/
theorem lexcover_zero (p : ℕ) [Fact p.Prime] (θ : ZMod p) (lamv : Fin s → ZMod p)
    (zθ : Fin s → PowerSeries (ZMod p)) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (j : Fin s)
    (hj : j.val = 0) (hM : 1 ≤ M j) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin (lexWin p A M Bx) j) := by
  rw [lexcover_iff θ lamv zθ _ j (fun c h => lexWin_low p A M Bx h)]
  intro σ
  refine ⟨_, by rw [lexWin_own]; exact ⟨-(A j : ℤ), by omega, le_rfl, rfl⟩, fun c hc => ?_⟩
  exact absurd hc (by rw [Fin.lt_def]; omega)

/-- **`lem:lexcover`** (lattice form): for ordered windows, with integers `κ̂_c ≡ κ_{c←j}` (`c < j`), column
`j` satisfies (ii) iff `𝓑_j + L_j = ℤ^{1+j}`: every `z ∈ ℤ^{1+j}` (coordinates `j` and `c < j` of `z`) is
`b + t (1, κ̂) + p y` with `b ∈ 𝓑_j = Wo^{(j)} × ∏_{c<j} [-B_{c←j}, B_{c←j}]`, `t ∈ ℤ`, `y ∈ ℤ^{1+j}`
(`L_j = ℤ(1, κ̂_0, …, κ̂_{j-1}) + pℤ^{1+j}`). -/
theorem lexcover_lattice (p : ℕ) [Fact p.Prime] (θ : ZMod p) (lamv : Fin s → ZMod p)
    (zθ : Fin s → PowerSeries (ZMod p)) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (j : Fin s)
    (κh : Fin s → ℤ) (hκ : ∀ c, c < j → (κh c : ZMod p) = kapL θ lamv zθ c j) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin (lexWin p A M Bx) j) ↔
      ∀ z : Fin s → ℤ, ∃ b : Fin s → ℤ,
        (-((A j : ℤ) + M j - 1) ≤ b j ∧ b j ≤ -(A j : ℤ)) ∧
        (∀ c, c < j → -(Bx c j : ℤ) ≤ b c ∧ b c ≤ Bx c j) ∧
        ∃ (t : ℤ) (y : Fin s → ℤ), z j = b j + t + p * y j ∧
          ∀ c, c < j → z c = b c + t * κh c + p * y c := by
  classical
  rw [lexcover_iff θ lamv zθ _ j (fun c h => lexWin_low p A M Bx h)]
  constructor
  · intro hcov z
    obtain ⟨o, ho, hc⟩ := hcov (fun c => ((z c - z j * κh c : ℤ) : ZMod p))
    rw [lexWin_own] at ho
    obtain ⟨oh, ho1, ho2, rfl⟩ := ho
    have hc' : ∀ c, c < j → ∃ b : ℤ, -(Bx c j : ℤ) ≤ b ∧ b ≤ Bx c j ∧
        (b : ZMod p) = ((z c - z j * κh c : ℤ) : ZMod p) + (oh : ZMod p) * kapL θ lamv zθ c j := by
      intro c h
      have := hc c h
      rw [lexWin_up p A M Bx h] at this
      exact this
    choose bf hb1 hb2 hb3 using hc'
    have hdvd : ∀ c (h : c < j), (p : ℤ) ∣ z c - bf c h - (z j - oh) * κh c := by
      intro c h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hb3 c h, ← hκ c h]; push_cast; ring
    choose yf hy using hdvd
    refine ⟨fun c => if h : c < j then bf c h else oh, by dsimp only; rw [dif_neg (lt_irrefl j)]; exact ⟨ho1, ho2⟩,
      fun c h => by simp only [dif_pos h]; exact ⟨hb1 c h, hb2 c h⟩,
      z j - oh, fun c => if h : c < j then yf c h else 0, by simp, fun c h => ?_⟩
    simp only [dif_pos h]
    linarith [hy c h]
  · intro hlat σ
    obtain ⟨b, hbj, hbc, t, y, hzj, hzc⟩ := hlat (fun c => if c = j then 0 else ((σ c).val : ℤ))
    refine ⟨(b j : ZMod p), by rw [lexWin_own]; exact ⟨b j, hbj.1, hbj.2, rfl⟩, fun c h => ?_⟩
    rw [lexWin_up p A M Bx h]
    refine ⟨b c, (hbc c h).1, (hbc c h).2, ?_⟩
    have h1 := congrArg (fun x : ℤ => (x : ZMod p)) (hzc c h)
    have h2 := congrArg (fun x : ℤ => (x : ZMod p)) hzj
    simp only [if_neg (ne_of_lt h)] at h1 h2
    push_cast at h1 h2
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero] at h1
    rw [ZMod.natCast_self, zero_mul, add_zero] at h2
    rw [← hκ c h, h1]
    linear_combination (κh c : ZMod p) * h2

end Cover

end GeoSeq
