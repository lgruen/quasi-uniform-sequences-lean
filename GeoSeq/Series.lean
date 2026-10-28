/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SeriesDefs

@[expose] public section

/-!
# GeoSeq stage S1: the bridge from truncated lists to `PowerSeries`

`TRep D L φ` (`L` gives the first `D` coefficients of `φ`) is preserved by every operation of
`GeoSeq/SeriesDefs.lean`: sums, scalar multiples, products (`tmul_rep`: the coefficient formula of a
product), inverses (`tinv_rep`: the recursion of `PowerSeries.coeff_inv`), the square root `√(1 + a x)`
(`tsqrt_rep`: the recursion of `sqrtCoeff`), the powers (`tpows_rep`), and hence the generator entries
of a self-similar scramble (`ssGen_entry`, `ssScr_entry`).
-/

namespace GeoSeq

open Finset PowerSeries

variable {R : Type*} [CommRing R]

lemma lsum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma lget_map_range (f : ℕ → R) {D n : ℕ} (h : n < D) : lget ((List.range D).map f) n = f n := by
  unfold lget
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

lemma lget_append_left (L : List R) (x : R) {n : ℕ} (h : n < L.length) :
    lget (L ++ [x]) n = lget L n := by
  unfold lget
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma lget_append_right (L : List R) (x : R) : lget (L ++ [x]) L.length = x := by
  unfold lget
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma lget_append_len (L : List R) (x : R) {n : ℕ} (h : L.length = n) : lget (L ++ [x]) n = x := by
  subst h; exact lget_append_right L x

/-! ## The ring operations -/

lemma tconst_rep (D : ℕ) (c : R) : TRep D (tconst D c) (C c) := by
  intro n hn; rw [tconst, lget_map_range _ hn, coeff_C]

lemma tone_rep (D : ℕ) : TRep D (tconst D (1 : R)) 1 := by
  intro n hn; rw [tconst, lget_map_range _ hn, coeff_one]

lemma tX_rep (D : ℕ) : TRep D (tX D) (X : PowerSeries R) := by
  intro n hn; rw [tX, lget_map_range _ hn, coeff_X]

lemma tadd_rep {D : ℕ} {a b : List R} {φ ψ : PowerSeries R} (ha : TRep D a φ) (hb : TRep D b ψ) :
    TRep D (tadd D a b) (φ + ψ) := by
  intro n hn; rw [tadd, lget_map_range _ hn, map_add, ha n hn, hb n hn]

lemma tsub_rep {D : ℕ} {a b : List R} {φ ψ : PowerSeries R} (ha : TRep D a φ) (hb : TRep D b ψ) :
    TRep D (tsub D a b) (φ - ψ) := by
  intro n hn; rw [tsub, lget_map_range _ hn, map_sub, ha n hn, hb n hn]

lemma tscale_rep {D : ℕ} (c : R) {a : List R} {φ : PowerSeries R} (ha : TRep D a φ) :
    TRep D (tscale D c a) (C c * φ) := by
  intro n hn; rw [tscale, lget_map_range _ hn, coeff_C_mul, ha n hn]

/-- **Products**: `[x^n](φ ψ) = ∑_{i ≤ n} [x^i]φ [x^{n-i}]ψ`. -/
lemma tmul_rep {D : ℕ} {a b : List R} {φ ψ : PowerSeries R} (ha : TRep D a φ) (hb : TRep D b ψ) :
    TRep D (tmul D a b) (φ * ψ) := by
  intro n hn
  rw [tmul, lget_map_range _ hn, lsum_range, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [ha i (by omega), hb (n - i) (by omega)]

/-! ## Inverses -/

lemma tinvAux_length (c : R) (a : List R) (n : ℕ) : (tinvAux c a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tinvAux, ih]

lemma tinvAux_stable (c : R) (a : List R) (n : ℕ) :
    ∀ N, n < N → lget (tinvAux c a N) n = lget (tinvAux c a (n + 1)) n := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hN with h | h
    · rw [show tinvAux c a (N + 1) = tinvAux c a N ++ _ from rfl,
        lget_append_left _ _ (by rw [tinvAux_length]; exact h), ih h]
    · rw [h]

/-- **Inverses** (`PowerSeries.coeff_inv`): given `c · a_0 = 1`, `tinv D c a` represents `φ⁻¹`. -/
lemma tinv_rep {K : Type*} [Field K] {D : ℕ} {a : List K} {φ : PowerSeries K} (ha : TRep D a φ)
    (c : K) (hc : 0 < D → c * lget a 0 = 1) : TRep D (tinv D c a) φ⁻¹ := by
  have hc' : 0 < D → c = (constantCoeff φ)⁻¹ := fun hD => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← ha 0 hD]
    exact eq_inv_of_mul_eq_one_left (hc hD)
  have key : ∀ n, n < D → lget (tinvAux c a (n + 1)) n = coeff n φ⁻¹ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rw [show tinvAux c a (n + 1) = tinvAux c a n ++ _ from rfl]
      rw [lget_append_len _ _ (tinvAux_length c a n), coeff_inv, ← hc' (by omega)]
      by_cases h0 : n = 0
      · simp [h0]
      · simp only [h0, if_false]
        congr 1
        rw [lsum_range, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
        simp only [Nat.sub_zero, lt_irrefl, if_false, add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        rw [if_pos (by omega), ha (i + 1) (by omega),
          tinvAux_stable c a (n - 1 - i) n (by omega), ih (n - 1 - i) (by omega) (by omega),
          show n - (i + 1) = n - 1 - i by omega]
  intro n hn
  rw [tinv, tinvAux_stable c a n D hn, key n hn]

/-! ## The square root `√(1 + a x)` over `ℤ/pℤ` -/

lemma tsqrtAux_length {p : ℕ} (a h : ZMod p) (n : ℕ) : (tsqrtAux a h n).length = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | m + 2, ih => simp [tsqrtAux, ih (m + 1) (by omega)]

lemma tsqrtAux_stable {p : ℕ} (a h : ZMod p) (n : ℕ) :
    ∀ N, n < N → lget (tsqrtAux a h N) n = lget (tsqrtAux a h (n + 1)) n := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hN with h' | h'
    · match N, ih, h' with
      | 0, _, h' => omega
      | M + 1, ih, h' =>
        rw [show tsqrtAux a h (M + 1 + 1) = tsqrtAux a h (M + 1) ++ _ from rfl,
          lget_append_left _ _ (by rw [tsqrtAux_length]; exact h'), ih h']
    · rw [h']

/-- **`√(1 + a x)`**: `tsqrtAux a h N` lists the coefficients `sqrtCoeff p a n`, `n < N`, given
`h = 1/2`. -/
lemma tsqrt_spec {p : ℕ} (a h : ZMod p) (hh : h = (2 : ZMod p)⁻¹) :
    ∀ n N, n < N → lget (tsqrtAux a h N) n = sqrtCoeff p a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hN
    rw [tsqrtAux_stable a h n N hN]
    match n, ih with
    | 0, _ => rw [sqrtCoeff]; rfl
    | m + 1, ih =>
      rw [show tsqrtAux a h (m + 1 + 1) = tsqrtAux a h (m + 1) ++ _ from rfl]
      rw [lget_append_len _ _ (tsqrtAux_length a h (m + 1)), sqrtCoeff, ← hh, lsum_range,
        ← Fin.sum_univ_eq_sum_range (fun i => lget (tsqrtAux a h (m + 1)) (i + 1) *
          lget (tsqrtAux a h (m + 1)) (m - i)) m]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.isLt
      rw [ih (i + 1) (by omega) (m + 1) (by omega), ih (m - i) (by omega) (m + 1) (by omega)]

lemma tsqrt_rep {p : ℕ} (a h : ZMod p) (hh : h = (2 : ZMod p)⁻¹) (D : ℕ) :
    TRep D (tsqrtAux a h D) (rhoWF p a) := by
  intro n hn
  rw [tsqrt_spec a h hh n D hn, rhoWF, coeff_mk]

/-! ## Powers and generator entries -/

lemma tpowsAux_rep {D : ℕ} {z : List R} {ζ : PowerSeries R} (hz : TRep D z ζ) :
    ∀ K (Z : List R) (ψ : PowerSeries R), TRep D Z ψ → ∀ k < K,
      TRep D ((tpowsAux D z Z K).getD k []) (ψ * ζ ^ k) := by
  intro K
  induction K with
  | zero => intro _ _ _ k hk; omega
  | succ K ih =>
    intro Z ψ hZ k hk
    match k with
    | 0 => simpa [tpowsAux] using hZ
    | k + 1 =>
      have := ih (tmul D Z z) (ψ * ζ) (tmul_rep hZ hz) k (by omega)
      simpa [tpowsAux, pow_succ', mul_assoc] using this

lemma tpows_rep {D : ℕ} {z : List R} {ζ : PowerSeries R} (hz : TRep D z ζ) (K k : ℕ) (hk : k < K) :
    TRep D ((tpows D z K).getD k []) (ζ ^ k) := by
  have := tpowsAux_rep hz K (tconst D 1) 1 (tone_rep D) k hk
  rw [one_mul] at this
  exact this

lemma tpowsAux_length (D : ℕ) (z : List R) : ∀ (K : ℕ) (Z : List R), (tpowsAux D z Z K).length = K := by
  intro K; induction K with
  | zero => intro _; rfl
  | succ K ih => intro Z; simp [tpowsAux, ih]

lemma tcols_length (D K : ℕ) (g z : List R) : (tcols D K g z).length = K := by
  rw [tcols, List.length_map, tpows, tpowsAux_length]

lemma tcols_getD (D K : ℕ) (g z : List R) (k : ℕ) (hk : k < K) :
    (tcols D K g z).getD k [] = tmul D g ((tpows D z K).getD k []) := by
  have hlen : ∀ K' (Z : List R), (tpowsAux D z Z K').length = K' := by
    intro K'; induction K' with
    | zero => intro _; rfl
    | succ K' ih => intro Z; simp [tpowsAux, ih]
  have hl : k < (tpows D z K).length := by rw [tpows, hlen]; exact hk
  unfold tcols
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hl]
  rfl

/-- **Generator entries of a self-similar scramble**: `[x^n] g_c z_c^k = cget (tcols D K g z) k n`. -/
lemma ssGen_entry {s : ℕ} (g zθ : Fin s → PowerSeries R) (c : Fin s) {D K : ℕ} {gL zL : List R}
    (hg : TRep D gL (g c)) (hz : TRep D zL (zθ c)) (n k : ℕ) (hn : n < D) (hk : k < K) :
    ssGen g zθ c n k = cget (tcols D K gL zL) k n := by
  rw [cget, tcols_getD D K gL zL k hk, tmul_rep hg (tpows_rep hz K k hk) n hn]
  rfl

/-- **Entries of the scramble `L_c` of a self-similar scramble**:
`[x^n] g_c (z_c - a_c)^i = cget (tcols D K g (z - a)) i n`, `a = z_c(0) = lget z 0`. -/
lemma ssScr_entry {s : ℕ} (g zθ : Fin s → PowerSeries R) (c : Fin s) {D K : ℕ} {gL zL : List R}
    (hg : TRep D gL (g c)) (hz : TRep D zL (zθ c)) (hD : 0 < D) (n i : ℕ) (hn : n < D)
    (hi : i < K) :
    ssScr g zθ c n i = cget (tcols D K gL (tsub D zL (tconst D (lget zL 0)))) i n := by
  have ha : lget zL 0 = constantCoeff (zθ c) := by
    rw [hz 0 hD, coeff_zero_eq_constantCoeff_apply]
  rw [cget, tcols_getD D K _ _ i hi,
    tmul_rep hg (tpows_rep (tsub_rep hz (tconst_rep D (lget zL 0))) K i hi) n hn, ha]
  rfl

end GeoSeq
