import Definitions.Def_TripodCanonicalHighHeightInputs
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Tactic.Push
import Definitions.Def_TripodLegendreHeightBasics
import Mathlib.Tactic.Tauto
import Definitions.Def_TripodLegendreHeightComparisonInputs

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:258-436.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

variable {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) {l : R}

/-- The right-hand side of the ultrametric comparison at a finite place:
`2(max(0, log v(λ)) + max(0, −log v(λ)) + max(0, −log v(λ − 1)))`. -/
def legendreBound (l : R) : ℤ :=
  2 * (max 0 (log (v l)) + max 0 (-log (v l)) + max 0 (-log (v (l - 1))))

lemma legendreBound_nonneg (l : R) : 0 ≤ legendreBound v l := by
  unfold legendreBound
  have h1 := le_max_left 0 (log (v l))
  have h2 := le_max_left 0 (-log (v l))
  have h3 := le_max_left 0 (-log (v (l - 1)))
  omega

variable (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- `v(legendreJ λ) ≠ 0 ↔ v(λ² − λ + 1) ≠ 0`. -/
lemma valuation_legendreJ_ne_zero_iff [NeZero (2 : R)] :
    v (legendreJ l) ≠ 0 ↔ v (l ^ 2 - l + 1) ≠ 0 := by
  have h256 : (256 : R) ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow]
  rw [div_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by norm_num),
    pow_ne_zero_iff (by norm_num), pow_ne_zero_iff (by norm_num)]
  simp only [(Valuation.ne_zero_iff v).mpr h256, (Valuation.ne_zero_iff v).mpr hl0,
    (Valuation.ne_zero_iff v).mpr hl1', ne_eq, not_false_eq_true, true_and, and_true]

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendreJ [NeZero (2 : R)] (hc : v (l ^ 2 - l + 1) ≠ 0) :
    log (v (legendreJ l)) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  have h256 : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit hl0 hl1 in
/-- **The ultrametric case analysis** for `λ`, `λ − 1`, `λ² − λ + 1` at a finite place. -/
lemma legendre_valuation_cases :
    (v l < 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) < 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) ≤ 1) ∨
    (1 < v l ∧ v (l - 1) = v l ∧ v (l ^ 2 - l + 1) = v l ^ 2) := by
  have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rcases lt_trichotomy (v l) 1 with hlt | heq | hgt
  · left
    have hb : v (l - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right v (by rw [map_one]; exact hlt), map_one]
    refine ⟨hlt, hb, ?_⟩
    have hlt' : v (l * (l - 1)) < v 1 := by
      rw [map_mul, hb, mul_one, map_one]
      exact hlt
    rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
  · have hb' : v (l - 1) ≤ 1 := by
      have := Valuation.map_sub v l 1
      rwa [heq, map_one, max_self] at this
    rcases hb'.lt_or_eq with hb | hb
    · right; left
      refine ⟨heq, hb, ?_⟩
      have hlt' : v (l * (l - 1)) < v 1 := by
        rw [map_mul, heq, one_mul, map_one]
        exact hb
      rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
    · right; right; left
      refine ⟨heq, hb, ?_⟩
      rw [e]
      refine (Valuation.map_add v _ _).trans (max_le ?_ (map_one v).le)
      rw [map_mul, heq, hb, mul_one]
  · right; right; right
    have hb : v (l - 1) = v l :=
      Valuation.map_sub_eq_of_lt_left v (by rw [map_one]; exact hgt)
    refine ⟨hgt, hb, ?_⟩
    have e' : l ^ 2 - l + 1 = l ^ 2 + (1 - l) := by ring
    have hlt' : v (1 - l) < v (l ^ 2) := by
      rw [Valuation.map_sub_swap, hb, map_pow]
      exact lt_self_pow₀ hgt (by norm_num)
    rw [e', Valuation.map_add_eq_of_lt_left v hlt', map_pow]

/-- **The upper bound** `max(0, log v(j)) ≤ legendreBound` for `v(256) ≤ 1`. -/
lemma max_log_valuation_legendreJ_le [NeZero (2 : R)] (h256 : v 256 ≤ 1) :
    max 0 (log (v (legendreJ l))) ≤ legendreBound v l := by
  refine max_le (legendreBound_nonneg v l) ?_
  by_cases hj : v (legendreJ l) = 0
  · rw [hj, log_zero]
    exact legendreBound_nonneg v l
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  have h256' : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendreJ v hl0 hl1 hc]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    have := le_max_left 0 (log (v l))
    have := le_max_right 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    have := le_max_right 0 (-log (v (l - 1)))
    omega
  · have hS : log (v (l ^ 2 - l + 1)) ≤ 0 := by
      have := (log_le_log hc one_ne_zero).mpr hc'
      simpa using this
    rw [ha, hb, log_one]
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    have := le_max_right 0 (log (v l))
    have := le_max_left 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    push_cast
    omega



end AbcAdaptation.Tripod

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: LocalTheory.lean:52-65; Places.lean:77; Ordp.lean:39-105; TwoAdic.lean:459,494; BadPlaceNorm.lean:28; LogCond.lean:50; Height.lean:120-132.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

noncomputable def inertDeg (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ





noncomputable abbrev completionAt (K : Type*) [Field K] [NumberField K]
    (w : FinitePlace K) := w.maximalIdeal.adicCompletion K

section
variable {k : Type*} [Field k] [NumberField k]
lemma residueChar_prime (w : FinitePlace k) : (residueChar w).Prime := by
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 k ⧸ w.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.maximalIdeal.ne_bot
  exact CharP.char_is_prime (𝓞 k ⧸ w.maximalIdeal.asIdeal) (ringChar _)
end

section
variable {K : Type*} [Field K] [NumberField K]
lemma under_int_eq (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.under ℤ = Ideal.span {(residueChar v : ℤ)} := by
  set P := v.maximalIdeal.asIdeal
  have hp : (residueChar v).Prime := residueChar_prime v
  haveI : CharP (𝓞 K ⧸ P) (residueChar v) := ringChar.charP _
  have hmem : (residueChar v : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.natCast_mem_of_charP_quotient (residueChar v) P
  have hle : Ideal.span {(residueChar v : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  haveI hprime : (Ideal.span {(residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hmax : (Ideal.span {(residueChar v : ℤ)}).IsMaximal :=
    IsPrime.to_maximal_ideal (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero)
  haveI : (P.under ℤ).IsPrime := Ideal.comap_isPrime _ _
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm





/-- The prime of a finite place lies over `(p)`, `p` its residue characteristic. -/
lemma liesOver_span_residueChar (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.LiesOver (Ideal.span {(residueChar v : ℤ)}) :=
  ⟨(under_int_eq v).symm⟩

/-- `N(𝔭_v) = p^{f_v}`. -/
lemma absNorm_eq_pow_residueChar (v : FinitePlace K) :
    Ideal.absNorm v.maximalIdeal.asIdeal = residueChar v ^ inertDeg K v := by
  haveI := liesOver_span_residueChar v
  exact (Ideal.pow_inertiaDeg (residueChar v) v.maximalIdeal.asIdeal).symm

/-- `f_v > 0`. -/
lemma inertDeg_pos' (v : FinitePlace K) : 0 < inertDeg K v :=
  Ideal.inertiaDeg_pos v.maximalIdeal.asIdeal ℤ



/-- The norm of an element of valuation `exp m` is `(p^{f_v})^m`. -/
lemma norm_eq_zpow_of_valued (v : FinitePlace K) (x : completionAt K v) (m : ℤ)
    (hx : Valued.v x = exp m) :
    ‖x‖ = ((residueChar v : ℝ) ^ inertDeg K v) ^ m := by
  rw [FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  have h : (WithZero.unzero (exp_ne_zero (a := m))).toAdd = m := rfl
  rw [h, NNReal.coe_zpow, NNReal.coe_natCast, absNorm_eq_pow_residueChar, Nat.cast_pow]
end

section
variable {k : Type*} [Field k] [NumberField k]

end

theorem log_apply_eq {T : Type*} [Field T] [NumberField T] (𝔭 : FinitePlace T) {y : T}
    (hy : y ≠ 0) :
    Real.log (𝔭 y) = ((log (𝔭.maximalIdeal.valuation T y) : ℤ) : ℝ) *
      (inertDeg T 𝔭 * Real.log (residueChar 𝔭)) := by
  have hv : 𝔭.maximalIdeal.valuation T y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  rw [← FinitePlace.norm_embedding_eq,
    norm_eq_zpow_of_valued 𝔭 _ (log (𝔭.maximalIdeal.valuation T y)) (by
      rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', exp_log hv]),
    Real.log_zpow, Real.log_pow]

theorem valuation_256_le_one {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) :
    w.maximalIdeal.valuation T 256 ≤ 1 := by
  have : (256 : T) = algebraMap (𝓞 T) T 256 := by rw [map_ofNat]
  rw [this]
  exact valuation_le_one _ _
section
variable {T : Type*} [Field T] [NumberField T]


noncomputable def finWeight (w : FinitePlace T) : ℝ := inertDeg T w * Real.log (residueChar w)

lemma finWeight_pos (w : FinitePlace T) : 0 < finWeight w :=
  mul_pos (by exact_mod_cast inertDeg_pos' w)
    (Real.log_pos (by exact_mod_cast (residueChar_prime w).one_lt))

/-- `log⁺|y|_w = f_w log p_w · max(0, log v_w(y))`. -/
lemma posLog_apply_eq (w : FinitePlace T) {y : T} (hy : y ≠ 0) :
    log⁺ (w y) = finWeight w * max 0 ((log (w.maximalIdeal.valuation T y) : ℤ) : ℝ) := by
  rw [Real.posLog_apply, log_apply_eq w hy, mul_max_of_nonneg _ _ (finWeight_pos w).le,
    mul_zero, mul_comm]
  rfl
end


end AbcAdaptation.Tripod

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:84-107,644-653,673-709.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

section
variable {T : Type*} [Field T] [NumberField T]
lemma support_posLog_subset (y : T) :
    Function.support (fun v : FinitePlace T => log⁺ (v y)) ⊆
      Function.mulSupport (fun v : FinitePlace T => v y) := by
  intro v hv
  simp only [Function.mem_support, Function.mem_mulSupport] at hv ⊢
  intro h
  apply hv
  rw [h, Real.posLog_one]

/-- `v ↦ log⁺|y|_v` has finite support. -/
lemma hasFiniteSupport_posLog (y : T) :
    Function.HasFiniteSupport (fun v : FinitePlace T => log⁺ (v y)) := by
  by_cases hy : y = 0
  · subst hy
    refine Set.Finite.subset Set.finite_empty ?_
    intro v hv
    simp at hv
  · exact Set.Finite.subset (FinitePlace.hasFiniteMulSupport hy) (support_posLog_subset y)

/-- `h_fin(y)` as a sum over any finite set containing the support. -/
lemma finHeight_eq_sum {y : T} {S : Finset (FinitePlace T)}
    (hS : ∀ v : FinitePlace T, log⁺ (v y) ≠ 0 → v ∈ S) :
    finHeight y = ∑ v ∈ S, log⁺ (v y) :=
  finsum_eq_sum_of_support_subset _ fun v hv => hS v hv


end

variable {K : CompactlyBounded} {x : Pt}



noncomputable def suppFinset (x : Pt) : Finset (FinitePlace (fieldOf x.1)) :=
  (Set.Finite.union
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1)) (hasFiniteSupport_posLog (gen x.1)⁻¹))
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1 - 1)⁻¹)
      (hasFiniteSupport_posLog (legendreJ (gen x.1))))).toFinset

lemma mem_suppFinset_of_ne {v : FinitePlace (fieldOf x.1)}
    (h : log⁺ (v (gen x.1)) ≠ 0 ∨ log⁺ (v (gen x.1)⁻¹) ≠ 0 ∨
      log⁺ (v (gen x.1 - 1)⁻¹) ≠ 0 ∨ log⁺ (v (legendreJ (gen x.1))) ≠ 0) :
    v ∈ suppFinset x := by
  rw [suppFinset, Set.Finite.mem_toFinset]
  simp only [Set.mem_union, Function.mem_support]
  tauto

lemma finHeight_gen_eq_sum (x : Pt) :
    finHeight (gen x.1) = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inl hv)

lemma finHeight_gen_inv_eq_sum (x : Pt) :
    finHeight (gen x.1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inl hv))

lemma finHeight_gen_sub_one_inv_eq_sum (x : Pt) :
    finHeight (gen x.1 - 1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1 - 1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inl hv)))

lemma finHeight_legendreJ_eq_sum (x : Pt) :
    finHeight (legendreJ (gen x.1)) = ∑ v ∈ suppFinset x, log⁺ (v (legendreJ (gen x.1))) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inr hv)))

/-- The sum of the three finite parts as a sum over `suppFinset`. -/
lemma two_mul_finHeight_sum_eq (x : Pt) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) =
      ∑ v ∈ suppFinset x,
        2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) := by
  rw [finHeight_gen_eq_sum, finHeight_gen_inv_eq_sum, finHeight_gen_sub_one_inv_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]

end AbcAdaptation.Tripod

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:439-486.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

variable {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) {l : T}
  (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- The three terms of the comparison at a finite place, in terms of the valuation. -/
lemma posLog_terms_eq :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) =
      finWeight w * (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [posLog_apply_eq w hl0, posLog_apply_eq w (inv_ne_zero hl0),
    posLog_apply_eq w (inv_ne_zero hl1'), map_inv₀, map_inv₀, log_inv, log_inv]
  unfold legendreBound
  push_cast
  ring

/-- **`log⁺|j|_w ≤ 2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w)`** at every finite place. -/
theorem posLog_legendreJ_le :
    log⁺ (w (legendreJ l)) ≤ 2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) := by
  rw [posLog_terms_eq w hl0 hl1]
  by_cases hj : legendreJ l = 0
  · rw [hj, map_zero, Real.posLog_zero]
    exact mul_nonneg (finWeight_pos w).le (by exact_mod_cast legendreBound_nonneg _ l)
  rw [posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h := max_log_valuation_legendreJ_le (w.maximalIdeal.valuation T) hl0 hl1
    (valuation_256_le_one w)
  have h' : ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) ≤
      (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'



end AbcAdaptation.Tripod

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:714-719; exact original parent LegendreFiniteUpperBound.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

theorem closedFiniteSource : LegendreFiniteUpperBound := by
  intro x
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  exact Finset.sum_le_sum fun v _ => posLog_legendreJ_le v (gen_ne_zero x.2.1) (gen_ne_one x)

end AbcAdaptation.Tripod

theorem solution : AbcAdaptation.Tripod.LegendreFiniteUpperBound := AbcAdaptation.Tripod.closedFiniteSource
