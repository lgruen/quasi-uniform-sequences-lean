/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs
public import GeoSeq.V94Defs

@[expose] public section

/-!
# GeoSeq stage V9-8 (paper V4, `sec:count`): definitions for exact digit relations

Over any field `F`, a frame of `s` places `a_c` and a scramble `L` (lower triangular, only `L_c[n][k]`, `k ≤ n`,
is used; `IsScramble`: nonzero diagonal).

* `frDigit a L c n V = y_{c,n}(V) = ∑_{k ≤ n} L_c[n][k] [(z - a_c)^k] V`, digit `n` of coordinate `c` of the point
  with index polynomial `V` (`lem:resform`(a); `frDigit_vecPoly` identifies it with the generator matrix
  `scrGen a L`).
* **Exact digit relations** (`def:exactrel`): a coefficient family `f : Fin s → ℕ → F` with `f_{c,n} = 0` for
  `n > T` and `relForm a L T f V = ∑_c ∑_{n ≤ T} f_{c,n} y_{c,n}(V) = 0` for every `V` with `deg V < m` (`relSpace a L T
  m`, the space of these families including `0`; an exact relation of top index `T` on `P_m` is a nonzero element,
  `IsExactRel`). Depth at most `J` at coordinate `c`: `f_{c,n} = 0` for `n < T - J` (`DepthAt`).
* **The polynomial of a relation** (`lem:reltype`): the place-`c` part `∑_n f_{c,n} η_{c,n}` of a relation is
  `relNum_c (z - a_c)^{-T-1} dz` with `relNum_c = ∑_{k ≤ T} g_{c,k} (z - a_c)^{T-k}`, `g_{c,k} = ∑_{k ≤ n ≤ T} f_{c,n}
  L_c[n][k]` (`relG`), and `Ξ = ∑_c relNum_c / (z - a_c)^{T+1} = A / w^{T+1}` with `A = ∑_c relNum_c w_c^{T+1}`
  (`relPoly`).
* Designs and skeleton relations (`cor:layer`, `cor:density`, `lem:rigid`): `skelVec n u` (the family of
  `∑_c u_c y_{c,n}`), `IsDesign` (a designed geometric digit), `AllDesigned`, `HasSkel`; the residue digits
  `resDig a c n V = Res_{a_c}(V w^{-n-1} dz)`.
* **Level-independent relations** (`prop:onerel`, `prop:blockrel`): `liEmbed J T ϑ` (the family
  `∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i}`), the spaces `liSpace` (valid at every level `T ≥ T₀`) and `classSpace` (at every
  level `T ≥ T₀` with `T ≡ j (mod ℓ)`).
* **Self-similar scrambles in residue form** (`lem:resform`(b), right-hand side): local multipliers `φ_c ∈ F[[t]]`
  (`t = z - a_c`), `y_{c,n}(V) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz) = θ^{n+1} [t^n] V(a_c + t) φ_c(t) w_c(a_c + t)^{-n-1}`;
  the scramble `ssL` (`L_c[n][k] = θ^{n+1} [t^{n-k}] φ_c w_c(a_c+t)^{-n-1}`).
-/

namespace GeoSeq

open Finset Polynomial

section Rel
variable {F : Type*} [Field F] {s : ℕ}

/-- The scramble has nonzero diagonal entries `L_c[n][n] ≠ 0` (a scramble of the frame, `lem:t0`). -/
def IsScramble (L : Fin s → ℕ → ℕ → F) : Prop := ∀ c n, L c n n ≠ 0

/-- Digit `n` of coordinate `c` of the scrambled frame, as a function of the index polynomial `V`:
`y_{c,n}(V) = ∑_{k ≤ n} L_c[n][k] [(z - a_c)^k] V`. -/
noncomputable def frDigit (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (c : Fin s) (n : ℕ) (V : F[X]) : F :=
  ∑ k ∈ range (n + 1), L c n k * (taylor (a c) V).coeff k

/-- The linear form `∑_c ∑_{n ≤ T} f_{c,n} y_{c,n}(V)` of a coefficient family of top index `T`. -/
noncomputable def relForm (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) (f : Fin s → ℕ → F) (V : F[X]) : F :=
  ∑ c, ∑ n ∈ range (T + 1), f c n * frDigit a L c n V

lemma relForm_add (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) (f g : Fin s → ℕ → F) (V : F[X]) :
    relForm a L T (f + g) V = relForm a L T f V + relForm a L T g V := by
  simp only [relForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma relForm_smul (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) (r : F) (f : Fin s → ℕ → F) (V : F[X]) :
    relForm a L T (r • f) V = r * relForm a L T f V := by
  simp only [relForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- **The space of exact digit relations of top index `T` on `P_m`, with `0`** (`def:exactrel`): families with
`f_{c,n} = 0` for `n > T` and `∑_c ∑_{n ≤ T} f_{c,n} y_{c,n}(V) = 0` for every index polynomial with `deg V < m`. -/
def relSpace (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T m : ℕ) : Submodule F (Fin s → ℕ → F) where
  carrier := {f | (∀ c n, T < n → f c n = 0) ∧ ∀ V : F[X], V.natDegree < m → relForm a L T f V = 0}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun c n h => ?_, fun V hV => ?_⟩
    · simp [hf1 c n h, hg1 c n h]
    · rw [relForm_add, hf2 V hV, hg2 V hV, add_zero]
  zero_mem' := by
    refine ⟨fun c n _ => rfl, fun V _ => ?_⟩
    simp [relForm]
  smul_mem' := by
    rintro r f ⟨hf1, hf2⟩
    refine ⟨fun c n h => ?_, fun V hV => ?_⟩
    · simp [hf1 c n h]
    · rw [relForm_smul, hf2 V hV, mul_zero]

/-- **An exact digit relation of top index `T` on `P_m`** (`def:exactrel`): a nonzero element of `relSpace`. -/
def IsExactRel (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T m : ℕ) (f : Fin s → ℕ → F) : Prop :=
  f ∈ relSpace a L T m ∧ f ≠ 0

/-- Depth at most `J` at coordinate `c` (`def:exactrel`): `f_{c,n} = 0` for `n < T - J`. -/
def DepthAt (T J : ℕ) (c : Fin s) (f : Fin s → ℕ → F) : Prop := ∀ n, n + J < T → f c n = 0

/-- The families whose coordinate-`c` coefficients vanish outside the digit positions `S`. -/
def colSupp (c : Fin s) (S : Finset ℕ) : Submodule F (Fin s → ℕ → F) where
  carrier := {f | ∀ n, n ∉ S → f c n = 0}
  add_mem' := by intro f g hf hg n hn; simp [hf n hn, hg n hn]
  zero_mem' := by intro n _; rfl
  smul_mem' := by intro r f hf n hn; simp [hf n hn]

/-- `g_{c,k} = ∑_{k ≤ n ≤ T} f_{c,n} L_c[n][k]`: the coefficients of the place-`c` part `∑_n f_{c,n} η_{c,n} =
∑_k g_{c,k} (z - a_c)^{-k-1} dz` of a relation (`lem:reltype`). -/
def relG (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (c : Fin s) (T k : ℕ) : F :=
  ∑ n ∈ range (T + 1), if k ≤ n then f c n * L c n k else 0

/-- The numerator `∑_{k ≤ T} g_{c,k} (z - a_c)^{T-k}` of the place-`c` part (pole order `≤ T + 1`). -/
noncomputable def relNum (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) (c : Fin s) : F[X] :=
  ∑ k ∈ range (T + 1), C (relG L f c T k) * (X - C (a c)) ^ (T - k)

/-- **The polynomial of a relation** (`lem:reltype`): `A = ∑_c relNum_c · w_c^{T+1}`, so that
`∑_c relNum_c (z - a_c)^{-T-1} = A / w^{T+1}`. -/
noncomputable def relPoly (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (f : Fin s → ℕ → F) (T : ℕ) : F[X] :=
  ∑ c, relNum a L f T c * wCo a c ^ (T + 1)

/-- The residue digits `ŷ_{c,n}(V) = Res_{a_c}(V w^{-n-1} dz)` (`sec:countskel`). -/
noncomputable def resDig (a : Fin s → F) (c : Fin s) (n : ℕ) (V : F[X]) : F :=
  locRes (a c) (n + 1) V (wCo a c ^ (n + 1))

/-- The family of `∑_c u_c y_{c,n}` (a skeleton relation when it holds on `P_{s(n+1)-1}`). -/
def skelVec (n : ℕ) (u : Fin s → F) : Fin s → ℕ → F := fun c k => if k = n then u c else 0

/-- **A designed geometric digit** of coordinate `i` at the full level `P_{sT}`, of depth at most `J`
(`sec:countdef`, example (1)): a relation of top index `T` on `P_{sT}` with `f_{i,T} = 1`, `f_{c,T} = 0` for
`c ≠ i`, and depth at most `J` at every coordinate (`y_{i,T} = -∑_c ∑_{T-J ≤ n < T} f_{c,n} y_{c,n}`). -/
def IsDesign (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (J T : ℕ) (i : Fin s) (f : Fin s → ℕ → F) : Prop :=
  f ∈ relSpace a L T (s * T) ∧ f i T = 1 ∧ (∀ c, c ≠ i → f c T = 0) ∧ ∀ c, DepthAt T J c f

/-- All `s` geometric digits of `P_{sT}` are designed with depth at most `J` (the set `E` of `cor:layer`). -/
def AllDesigned (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (J T : ℕ) : Prop := ∀ i, ∃ f, IsDesign a L J T i f

/-- `P_{s(T+1)-1}` satisfies a skeleton relation `∑_c u_c y_{c,T} = 0` with some `u ≠ 0` (the set `S` of
`cor:density`). -/
def HasSkel (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) : Prop :=
  ∃ u : Fin s → F, u ≠ 0 ∧ skelVec T u ∈ relSpace a L T (s * (T + 1) - 1)

/-- The family of `∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i}` (a level-independent relation read at level `T ≥ J`). -/
def liEmbed (J T : ℕ) (ϑ : Fin s → ℕ → F) : Fin s → ℕ → F :=
  fun c n => if n ≤ T ∧ T ≤ n + J then ϑ c (T - n) else 0

/-- **Level-independent relations** valid from `T₀` on (`prop:onerel`): families `ϑ_{c,i}` (`i ≤ J`) with
`∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i}(V) = 0` for every `T ≥ T₀` and `deg V < sT`. -/
def liSpace (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (J T₀ : ℕ) : Submodule F (Fin s → ℕ → F) where
  carrier := {ϑ | (∀ c i, J < i → ϑ c i = 0) ∧ ∀ T, T₀ ≤ T → liEmbed J T ϑ ∈ relSpace a L T (s * T)}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun c i h => by simp [hf1 c i h, hg1 c i h], fun T hT => ?_⟩
    have : liEmbed J T (f + g) = liEmbed J T f + liEmbed J T g := by
      funext c n; simp only [liEmbed, Pi.add_apply]; split_ifs <;> simp
    rw [this]; exact add_mem (hf2 T hT) (hg2 T hT)
  zero_mem' := by
    refine ⟨fun c i _ => rfl, fun T _ => ?_⟩
    have : liEmbed J T (0 : Fin s → ℕ → F) = 0 := by funext c n; simp [liEmbed]
    rw [this]; exact zero_mem _
  smul_mem' := by
    rintro r f ⟨hf1, hf2⟩
    refine ⟨fun c i h => by simp [hf1 c i h], fun T hT => ?_⟩
    have : liEmbed J T (r • f) = r • liEmbed J T f := by
      funext c n; simp only [liEmbed, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    rw [this]; exact Submodule.smul_mem _ r (hf2 T hT)

/-- **Level-independent relations of class `j`** (`prop:blockrel`): as `liSpace`, at every level `T ≥ T₀` with
`T ≡ j (mod ℓ)`. -/
def classSpace (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (ℓ j J T₀ : ℕ) : Submodule F (Fin s → ℕ → F) where
  carrier := {ϑ | (∀ c i, J < i → ϑ c i = 0) ∧
    ∀ T, T₀ ≤ T → T % ℓ = j → liEmbed J T ϑ ∈ relSpace a L T (s * T)}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun c i h => by simp [hf1 c i h, hg1 c i h], fun T hT hj => ?_⟩
    have : liEmbed J T (f + g) = liEmbed J T f + liEmbed J T g := by
      funext c n; simp only [liEmbed, Pi.add_apply]; split_ifs <;> simp
    rw [this]; exact add_mem (hf2 T hT hj) (hg2 T hT hj)
  zero_mem' := by
    refine ⟨fun c i _ => rfl, fun T _ _ => ?_⟩
    have : liEmbed J T (0 : Fin s → ℕ → F) = 0 := by funext c n; simp [liEmbed]
    rw [this]; exact zero_mem _
  smul_mem' := by
    rintro r f ⟨hf1, hf2⟩
    refine ⟨fun c i h => by simp [hf1 c i h], fun T hT hj => ?_⟩
    have : liEmbed J T (r • f) = r • liEmbed J T f := by
      funext c n; simp only [liEmbed, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    rw [this]; exact Submodule.smul_mem _ r (hf2 T hT hj)

/-- **A self-similar scramble in residue form** with scale `θ` and local multipliers `φ_c ∈ F[[t]]`, `t = z - a_c`
(`lem:resform`(b), right-hand side): `L_c[n][k] = θ^{n+1} [t^{n-k}] φ_c(t) w_c(a_c + t)^{-n-1}`, so that
`y_{c,n}(V) = θ^{n+1} [t^n] V(a_c + t) φ_c(t) w_c(a_c+t)^{-n-1} = Res_{a_c}(V φ_c (θ/w)^{n+1} dz)` (`ssL_digit`). -/
noncomputable def ssL (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) : Fin s → ℕ → ℕ → F :=
  fun c n k => θ ^ (n + 1) *
    PowerSeries.coeff (n - k) (φ c * ((taylor (a c) (wCo a c) : PowerSeries F)⁻¹) ^ (n + 1))

/-- The families of depth at most `J` at coordinate `c` (a subspace). -/
def depthSub (T J : ℕ) (c : Fin s) : Submodule F (Fin s → ℕ → F) where
  carrier := {f | DepthAt T J c f}
  add_mem' := by intro f g hf hg n hn; simp [hf n hn, hg n hn]
  zero_mem' := by intro n _; rfl
  smul_mem' := by intro r f hf n hn; simp [hf n hn]

/-- The family of the staggered relation `y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` (top index `T`, depth `1`). -/
def stagVec (cs : Fin s) (k : Fin s → F) (T : ℕ) : Fin s → ℕ → F :=
  fun c n => if c = cs then (if n = T then 1 else 0) else (if n + 1 = T then -k c else 0)

/-- `ϑ_c(w/θ) = ∑_{i ≤ J} ϑ_{c,i} (w/θ)^i`, a polynomial in `z`. -/
noncomputable def ϑpoly (a : Fin s → F) (θ : F) (J : ℕ) (ϑ : Fin s → ℕ → F) (c : Fin s) : F[X] :=
  ∑ i ∈ range (J + 1), C (ϑ c i) * (C θ⁻¹ * wPoly a) ^ i

end Rel

end GeoSeq
