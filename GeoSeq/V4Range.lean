/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4Defs

@[expose] public section

/-!
# GeoSeq stage V4: soundness of the archive range checker (`thm:LF`(a))

`lfOK_sound`: if `lfOK lo len B y1 y3 recs = true`, then every prime `p ∈ [lo, lo + len)` has an archived
design `D` valid at `p` (`odValid`) with `p < 10(p - Γ)` from `y1` on and `3p ≤ 10(p - Γ)` from `y3` on.
-/

namespace GeoSeq

variable {s : ℕ}

lemma lfSmallDiv_sound {n B : ℕ} (h : lfSmallDiv n B = true) : ¬ n.Prime := by
  intro hp
  obtain ⟨d, -, hd⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
  obtain ⟨⟨h2, hdn⟩, hmod⟩ := hd
  rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

theorem lfCover_sound (B : ℕ) : ∀ (k n : ℕ) (ps : List ℕ), lfCover B n k ps = true →
    ∀ m, n ≤ m → m < n + k → m.Prime → m ∈ ps := by
  intro k
  induction k with
  | zero => intro n ps _ m h1 h2; omega
  | succ k ih =>
    intro n ps h m h1 h2 hm
    cases ps with
    | nil =>
      simp only [lfCover, Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e; exact absurd hm (lfSmallDiv_sound h.1)
      · exact ih (n + 1) [] h.2 m e (by omega) hm
    | cons q qs =>
      simp only [lfCover] at h
      split_ifs at h with hq
      · rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; subst hq; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (n + 1) qs h m e (by omega) hm)
      · rw [Bool.and_eq_true] at h
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact absurd hm (lfSmallDiv_sound h.1)
        · exact ih (n + 1) (q :: qs) h.2 m e (by omega) hm

/-- **Soundness of the archive check**: every prime of the range has a valid archived ordered design with
the two thresholds. -/
theorem lfOK_sound (lo len B y1 y3 : ℕ) (recs : List (ODRec s)) (h : lfOK lo len B y1 y3 recs = true)
    (p : ℕ) (hp : p.Prime) (h1 : lo ≤ p) (h2 : p < lo + len) :
    ∃ D : ODesign s, odValid p D ∧ (y1 ≤ p → p < 10 * (p - odCost D p)) ∧
      (y3 ≤ p → 3 * p ≤ 10 * (p - odCost D p)) := by
  unfold lfOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hall, hcov⟩ := h
  have hm := lfCover_sound B len lo _ hcov p h1 h2 hp
  obtain ⟨r, hr, hrp⟩ := List.mem_map.mp hm
  have hok := List.all_eq_true.mp hall r hr
  unfold ODRec.ok at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at hok
  obtain ⟨⟨hv, hy1⟩, hy3⟩ := hok
  subst hrp
  refine ⟨r.D, hv, fun hy => ?_, fun hy => ?_⟩
  · rcases hy1 with h | h
    · exact absurd hy h
    · exact h
  · rcases hy3 with h | h
    · exact absurd hy h
    · exact h

end GeoSeq
