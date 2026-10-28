/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs
public import GeoSeq.Mesh

@[expose] public section

/-!
# GeoSeq stage V9-2 (part 2): the prefix lemma for level families (`lem:prefix`, `rem:prefixcases`)

* `prefix_sep_gap` (**`lem:prefix`**, separation): if `sep(P_m) ≥ LB` for every `m` of a level family
  with largest gap `≤ Δ`, then `δ(P_{[N]}) ≥ LB q^{-Δ/s} N^{-1/s}` for every `N ≥ 2` (as in the paper:
  the least family element `m'` with `q^{m'} ≥ N` has `q^{m'} ≤ q^Δ N`).
* The covering bound `h(P_{[N]}) ≤ √s q N^{-1/s}` is `prefix_cov` (`GeoSeq/Mesh.lean`, unchanged).
* `prefix_mesh_gap` (**`lem:prefix`**, mesh ratio): `h(P_{[N]}) ≤ √s q^{1+Δ/s}/LB · δ(P_{[N]})` for
  every `N ≥ 2` (`δ = 2 · sepRad`, toroidal), so the sequence is quasi-uniform.
* `hasGap_sN1`, `prefix_sep_sN1`, `prefix_mesh_sN1` (**`rem:prefixcases`**, the family
  `Λ = sℕ - 1 = {s-1, 2s-1, …}`, `Δ = s`): `δ(P_{[N]}) ≥ (LB/q) N^{-1/s}` and `h/δ ≤ √s q²/LB`.
  (The family `sℕ` is `prefix_sep`/`prefix_mesh` of `GeoSeq/Prefix.lean`, `GeoSeq/Mesh.lean`.)
-/

namespace GeoSeq

open Finset

variable {R : Type*} [CommRing R] {q s : ℕ}

lemma rpow_pow_inv_self (hq : 0 < q) (hs : 1 ≤ s) :
    (((q : ℝ) ^ s) ^ (-(1 / (s : ℝ)))) = (q : ℝ)⁻¹ := by
  rw [Real.rpow_neg (by positivity), one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]

lemma rpow_pow_self (hq : 0 < q) (hs : 1 ≤ s) :
    (((q : ℝ) ^ s) ^ (1 / (s : ℝ))) = (q : ℝ) := by
  rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]

/-- **`lem:prefix`** (separation half, level families): `sep(P_m) ≥ LB ≥ 0` for every `m` of a level
family with largest gap `≤ Δ` gives `δ(P_{[N]}) ≥ LB q^{-Δ/s} N^{-1/s}` for every `N ≥ 2`. -/
theorem prefix_sep_gap (q s : ℕ) (hq : 2 ≤ q) (pt : ℕ → Fin s → ℝ) (Lev : ℕ → Prop) (Δ : ℕ)
    (hgap : HasGap Lev Δ) (LB : ℝ) (hLB : 0 ≤ LB) (h : ∀ m, Lev m → SepAtPrefix q s m pt LB) :
    SepAllN s pt (LB * ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ)))) := by
  intro N hN v w hv hw hvw
  set m := Nat.log q (N - 1)
  have hlo : q ^ m ≤ N - 1 := Nat.pow_log_le_self q (by omega)
  have hhi : N - 1 < q ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) _
  obtain ⟨m', hm', hmm', hm'Δ⟩ := hgap m
  have hNm' : N ≤ q ^ m' := by
    have : q ^ (m + 1) ≤ q ^ m' := Nat.pow_le_pow_right (by omega) hmm'
    omega
  have hsep := h m' hm' v w (lt_of_lt_of_le hv hNm') (lt_of_lt_of_le hw hNm') hvw
  -- `q^{m'} ≤ q^Δ N`
  have hle : q ^ m' ≤ q ^ Δ * N := by
    calc q ^ m' ≤ q ^ (m + Δ) := Nat.pow_le_pow_right (by omega) hm'Δ
      _ = q ^ Δ * q ^ m := by rw [pow_add, mul_comm]
      _ ≤ q ^ Δ * N := Nat.mul_le_mul_left _ (by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hle' : ((q : ℝ) ^ m') ≤ (q : ℝ) ^ Δ * N := by exact_mod_cast hle
  have hs0 : -(1 / (s : ℝ)) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / (s : ℝ) := by positivity
    linarith
  have hmono : ((q : ℝ) ^ Δ * N) ^ (-(1 / (s : ℝ))) ≤ ((q : ℝ) ^ m') ^ (-(1 / (s : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle' hs0
  rw [Real.mul_rpow (by positivity) (by positivity)] at hmono
  calc LB * ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ))) * (N : ℝ) ^ (-(1 / (s : ℝ)))
      = LB * (((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ))) * (N : ℝ) ^ (-(1 / (s : ℝ)))) := by ring
    _ ≤ LB * ((q : ℝ) ^ m') ^ (-(1 / (s : ℝ))) := mul_le_mul_of_nonneg_left hmono hLB
    _ ≤ _ := hsep

/-- From `δ ≥ b N^{-1/s}` on index pairs to the separation radius of the point set `P_{[N]}`. -/
lemma sepAllN_sepRad (pt : ℕ → Fin s → ℝ) (b : ℝ) (hb : 0 < b) (hsep : SepAllN s pt b) (N : ℕ)
    (hN : 2 ≤ N) :
    b * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ 2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N pt) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbN : 0 < b * (N : ℝ) ^ (-(1 / (s : ℝ))) := mul_pos hb (Real.rpow_pos_of_pos hNpos _)
  have h01 : pt 0 ≠ pt 1 := by
    intro h
    have := hsep N hN 0 1 (by omega) (by omega) (by omega)
    rw [h] at this
    have h0 : Z3NetDGS.torDist2 (pt 1) (pt 1) = 0 := by
      simp [Z3NetDGS.torDist2, Z3NetDGS.torCoord]
    rw [h0] at this
    linarith
  have hmem : ∀ v, v < N → pt v ∈ prefixSet N pt := fun v hv =>
    Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, rfl⟩
  have : Nonempty {xy : (Fin s → ℝ) × (Fin s → ℝ) // xy.1 ∈ prefixSet N pt ∧
      xy.2 ∈ prefixSet N pt ∧ xy.1 ≠ xy.2} :=
    ⟨⟨(pt 0, pt 1), hmem 0 (by omega), hmem 1 (by omega), h01⟩⟩
  have : b * (N : ℝ) ^ (-(1 / (s : ℝ))) / 2 ≤
      Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N pt) := by
    apply le_ciInf
    rintro ⟨⟨x, y⟩, hx, hy, hxy⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hvw : v ≠ w := fun h => hxy (by rw [h])
    have := hsep N hN v w (Finset.mem_range.mp hv) (Finset.mem_range.mp hw) hvw
    show b * (N : ℝ) ^ (-(1 / (s : ℝ))) / 2 ≤ Z3NetDGS.torDist2 (pt v) (pt w) / 2
    linarith
  linarith

/-- **`lem:prefix`** (mesh ratio, level families): for a `(0,s)`-sequence with `sep(P_m) ≥ LB > 0` for
every `m` of a level family with largest gap `≤ Δ`, `h(P_{[N]}) ≤ √s q^{1+Δ/s}/LB · δ(P_{[N]})` for every
`N ≥ 2` (`h` Euclidean covering radius, `δ = 2 · sepRad` toroidal separation): quasi-uniform. -/
theorem prefix_mesh_gap [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ m, Lev m → SepAtPrefix q s m (seqPoint D C) LB) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q * ((q : ℝ) ^ Δ) ^ (1 / (s : ℝ)) / LB *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C))) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ : 0 < ((q : ℝ) ^ Δ) ^ (1 / (s : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hQinv : ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ))) = (((q : ℝ) ^ Δ) ^ (1 / (s : ℝ)))⁻¹ :=
    Real.rpow_neg (by positivity) _
  have hb : 0 < LB * ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ))) := by rw [hQinv]; positivity
  have hsep := sepAllN_sepRad (seqPoint D C) _ hb
    (prefix_sep_gap q s hq _ Lev Δ hgap LB hLB.le h) N hN
  have hcov := prefix_cov D C hq hs hseq N (by omega)
  have hfac : 0 ≤ Real.sqrt s * q * ((q : ℝ) ^ Δ) ^ (1 / (s : ℝ)) / LB := by positivity
  calc Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C))
      ≤ Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) := hcov
    _ = Real.sqrt s * q * ((q : ℝ) ^ Δ) ^ (1 / (s : ℝ)) / LB *
          (LB * ((q : ℝ) ^ Δ) ^ (-(1 / (s : ℝ))) * (N : ℝ) ^ (-(1 / (s : ℝ)))) := by
        rw [hQinv]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsep hfac

/-- The level family `sℕ - 1 = {s-1, 2s-1, …}` has largest gap `s` (`rem:prefixcases`; `s ≥ 2`). -/
lemma hasGap_sN1 (hs : 2 ≤ s) : HasGap (fun m => ∃ K, 1 ≤ K ∧ m = s * K - 1) s := by
  intro m
  set t := (m + 1) / s
  have h1 : m + 1 < s * (t + 1) := Nat.lt_mul_div_succ (m + 1) (show 0 < s by omega)
  have h2 : s * t ≤ m + 1 := Nat.mul_div_le (m + 1) s
  refine ⟨s * (t + 1) - 1, ⟨t + 1, Nat.le_add_left 1 t, rfl⟩, ?_, ?_⟩
  · rw [mul_add_one] at h1 ⊢
    generalize s * t = u at *
    omega
  · rw [mul_add_one]
    generalize s * t = u at *
    omega

/-- **`rem:prefixcases`**, family `sℕ - 1` (separation): `δ(P_{[N]}) ≥ (LB/q) N^{-1/s}`. -/
theorem prefix_sep_sN1 (q s : ℕ) (hq : 2 ≤ q) (hs : 2 ≤ s) (pt : ℕ → Fin s → ℝ) (LB : ℝ)
    (hLB : 0 ≤ LB) (h : ∀ K, 1 ≤ K → SepAtPrefix q s (s * K - 1) pt LB) :
    SepAllN s pt (LB / q) := by
  have := prefix_sep_gap q s hq pt _ s (hasGap_sN1 hs) LB hLB (by
    rintro m ⟨K, hK, rfl⟩; exact h K hK)
  rwa [rpow_pow_inv_self (by omega) (by omega), ← div_eq_mul_inv] at this

/-- **`rem:prefixcases`**, family `sℕ - 1` (mesh ratio): `h(P_{[N]}) ≤ √s q²/LB · δ(P_{[N]})`. -/
theorem prefix_mesh_sN1 [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K, 1 ≤ K → SepAtPrefix q s (s * K - 1) (seqPoint D C) LB) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * (q : ℝ) ^ 2 / LB *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C))) := by
  have := prefix_mesh_gap D C hq (by omega) hseq _ s (hasGap_sN1 hs) LB hLB (by
    rintro m ⟨K, hK, rfl⟩; exact h K hK) N hN
  rwa [rpow_pow_self (by omega) (by omega), mul_assoc (Real.sqrt s), ← sq] at this

end GeoSeq
