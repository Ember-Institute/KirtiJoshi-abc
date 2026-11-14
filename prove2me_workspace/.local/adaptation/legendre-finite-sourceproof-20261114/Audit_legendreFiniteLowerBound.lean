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
import Mathlib.Tactic.Positivity

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



/-- **The lower bound** `legendreBound ≤ max(0, log v(j))` for `v(256) = 1` and `j ≠ 0`. -/
lemma legendreBound_le_max_log_valuation_legendreJ [NeZero (2 : R)] (h256 : v 256 = 1)
    (hj : v (legendreJ l) ≠ 0) :
    legendreBound v l ≤ max 0 (log (v (legendreJ l))) := by
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [log_valuation_legendreJ v hl0 hl1 hc, h256, log_one]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    omega
  · rw [ha, hb, log_one]
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
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

noncomputable def ramIdx (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  Ideal.ramificationIdx w.maximalIdeal.asIdeal ℤ

noncomputable def localDeg (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  ramIdx K w * inertDeg K w

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

/-- The prime of `ℤ` below a finite place is nonzero. -/
lemma under_int_ne_bot (v : FinitePlace K) : v.maximalIdeal.asIdeal.under ℤ ≠ ⊥ := by
  rw [under_int_eq, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (residueChar_prime v).ne_zero

/-- The prime of `ℤ` below a finite place is maximal. -/
lemma under_int_isMaximal (v : FinitePlace K) : (v.maximalIdeal.asIdeal.under ℤ).IsMaximal := by
  have hp : (residueChar v).Prime := residueChar_prime v
  rw [under_int_eq]
  haveI : (Ideal.span {(residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  exact IsPrime.to_maximal_ideal (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero)

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

/-- `e_v > 0`. -/
lemma ramIdx_pos' (v : FinitePlace K) : 0 < ramIdx K v :=
  Ideal.ramificationIdx_pos v.maximalIdeal.asIdeal ℤ

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
lemma two_mem_maximalIdeal_iff (v : FinitePlace k) :
    (2 : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ residueChar v = 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h2 : (Ideal.Quotient.mk v.maximalIdeal.asIdeal (2 : 𝓞 k)) =
      ((2 : ℕ) : 𝓞 k ⧸ v.maximalIdeal.asIdeal) := by
    rw [map_ofNat, Nat.cast_ofNat]
  rw [h2, CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) Nat.prime_two
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


section
variable {T : Type*} [Field T] [NumberField T]
lemma valuation_two_eq_one_of_ne {w : FinitePlace T} (h2 : residueChar w ≠ 2) :
    w.maximalIdeal.valuation T 2 = 1 := by
  have : (2 : T) = algebraMap (𝓞 T) T 2 := by rw [map_ofNat]
  rw [this, valuation_eq_one_iff_notMem, two_mem_maximalIdeal_iff]
  exact h2

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

lemma posLog_finite_le (hx : x ∈ K.set) (v : FinitePlace (fieldOf x.1))
    (hv : residueChar v ∈ K.V) :
    log⁺ (v (gen x.1)) ≤ K.c ∧ log⁺ (v (gen x.1)⁻¹) ≤ K.c ∧
      log⁺ (v (gen x.1 - 1)⁻¹) ≤ K.c := by
  obtain ⟨h1, h2⟩ := hx.1 v hv
  refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h1
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h2

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



/-- **`2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w) ≤ log⁺|j|_w`** at a finite place of odd
residue characteristic, for `j ≠ 0`. -/
theorem posLog_legendreJ_ge (h2 : residueChar w ≠ 2) (hj : legendreJ l ≠ 0) :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) ≤ log⁺ (w (legendreJ l)) := by
  rw [posLog_terms_eq w hl0 hl1, posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h256 : w.maximalIdeal.valuation T 256 = 1 := by
    have : (256 : T) = 2 ^ 8 := by norm_num
    rw [this, map_pow, valuation_two_eq_one_of_ne h2, one_pow]
  have h := legendreBound_le_max_log_valuation_legendreJ (w.maximalIdeal.valuation T) hl0 hl1
    h256 ((Valuation.ne_zero_iff _).mpr hj)
  have h' : (legendreBound (w.maximalIdeal.valuation T) l : ℝ) ≤
      ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

end AbcAdaptation.Tripod

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: TwoAdic.lean:111-181; Height.lean:722-741.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

section
variable {K : Type*} [Field K] [NumberField K]
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : residueChar w = q) :
    localDeg K w = (Ideal.span {(q : ℤ)}).ramificationIdx' w.maximalIdeal.asIdeal *
      (Ideal.span {(q : ℤ)}).inertiaDeg' w.maximalIdeal.asIdeal := by
  subst hq
  rw [← under_int_eq]
  haveI : w.maximalIdeal.asIdeal.LiesOver (w.maximalIdeal.asIdeal.under ℤ) := inferInstance
  haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  unfold localDeg ramIdx inertDeg
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ w.maximalIdeal.asIdeal (under_int_ne_bot w),
    Ideal.inertiaDeg'_eq_inertiaDeg _ w.maximalIdeal.asIdeal]

/-- `∑_{w ∈ S, p_w = q} [K_w : ℚ_q] ≤ [K : ℚ]` for every finite set `S` of places of `K`
(from `∑_{w ∣ q} e_w f_w = [K : ℚ]`). -/
lemma sum_localDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
  classical
  by_cases hq : q.Prime
  · set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp
    haveI hmax : p.IsMaximal := by
      haveI hprime : p.IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
          (Nat.prime_iff_prime_int.1 hq)
      exact IsPrime.to_maximal_ideal (by
        rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero)
    have hp0 : p ≠ ⊥ := by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    have hsum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K hp0 (p := p)
    set T := S.filter (fun w => residueChar w = q) with hT
    have hover : ∀ w ∈ T, w.maximalIdeal.asIdeal.LiesOver p := by
      intro w hw
      rw [hT, Finset.mem_filter] at hw
      rw [hp, ← hw.2]
      exact liesOver_span_residueChar w
    have hsub : T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal) ⊆
        IsDedekindDomain.primesOverFinset p (𝓞 K) := by
      intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨w, hw, rfl⟩ := hP
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr
        ⟨inferInstance, hover w hw⟩
    have hinj : Set.InjOn (fun w : FinitePlace K => w.maximalIdeal.asIdeal) T := by
      intro w₁ _ w₂ _ h
      exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    calc ∑ w ∈ T, localDeg K w
        = ∑ w ∈ T, p.ramificationIdx' w.maximalIdeal.asIdeal *
            p.inertiaDeg' w.maximalIdeal.asIdeal := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hT, Finset.mem_filter] at hw
          exact localDeg_eq_ramificationIdx'_mul_inertiaDeg' w hw.2
      _ = ∑ P ∈ T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          (Finset.sum_image (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hinj).symm
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hsub
      _ = Module.finrank ℚ K := hsum
  · refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (Nat.zero_le _)
    intro w hw
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ residueChar_prime w) hq

/-- `∑_{w ∈ S, p_w = q} f_w ≤ [K : ℚ]` for every finite set `S` of places of `K`. -/
lemma sum_inertDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), inertDeg K w ≤ Module.finrank ℚ K := by
  refine le_trans (Finset.sum_le_sum fun w _ => ?_) (sum_localDeg_filter_le S q)
  unfold localDeg
  exact Nat.le_mul_of_pos_left _ (ramIdx_pos' w)
end

lemma card_filter_residueChar_mem_le (x : Pt) (S : Finset (FinitePlace (fieldOf x.1)))
    (V : Finset ℕ) :
    (S.filter (fun v => residueChar v ∈ V)).card ≤ V.card * deg x.1 := by
  classical
  have hsub : S.filter (fun v => residueChar v ∈ V) ⊆
      V.biUnion (fun q => S.filter (fun v => residueChar v = q)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_biUnion]
    exact ⟨_, hv.2, Finset.mem_filter.mpr ⟨hv.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun q _ => ?_
  calc (S.filter (fun v => residueChar v = q)).card
      = ∑ v ∈ S.filter (fun v => residueChar v = q), 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ v ∈ S.filter (fun v => residueChar v = q), inertDeg (fieldOf x.1) v :=
        Finset.sum_le_sum fun v _ => inertDeg_pos' v
    _ ≤ Module.finrank ℚ (fieldOf x.1) := sum_inertDeg_filter_le S q
    _ = deg x.1 := (deg_eq_finrank x.1).symm

end AbcAdaptation.Tripod

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:743-784; exact original parent LegendreFiniteLowerBound.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

theorem closedFiniteSource : LegendreFiniteLowerBound := by
  intro K x hx hj
  classical
  have hc := CompactlyBounded.c_nonneg hx
  have hg0 := gen_ne_zero x.2.1
  have hg1 := gen_ne_one x
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  set S := suppFinset x with hS
  set A : FinitePlace (fieldOf x.1) → ℝ := fun v =>
    2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) with hA
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => residueChar v ∈ K.V)]
  have hA_le : ∀ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v ≤ 6 * K.c := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨h1, h2, h3⟩ := posLog_finite_le hx v hv.2
    rw [hA]
    dsimp only
    linarith
  have hA_le' : ∀ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V),
      A v ≤ log⁺ (v (legendreJ (gen x.1))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h2 : residueChar v ≠ 2 := fun h => hv.2 (h ▸ K.two_mem)
    exact posLog_legendreJ_ge v hg0 hg1 h2 hj
  have hcard := card_filter_residueChar_mem_le x S K.V
  have hcard' : ((S.filter (fun v => residueChar v ∈ K.V)).card : ℝ) ≤ K.V.card * deg x.1 := by
    exact_mod_cast hcard
  calc ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v +
        ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), A v
      ≤ ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), 6 * K.c +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) :=
        add_le_add (Finset.sum_le_sum hA_le) (Finset.sum_le_sum hA_le')
    _ = 6 * K.c * (S.filter (fun v => residueChar v ∈ K.V)).card +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 6 * K.c * (K.V.card * deg x.1) + ∑ v ∈ S, log⁺ (v (legendreJ (gen x.1))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hcard' (by positivity)) ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Real.posLog_nonneg
    _ = _ := by ring

end AbcAdaptation.Tripod

theorem solution : AbcAdaptation.Tripod.LegendreFiniteLowerBound := AbcAdaptation.Tripod.closedFiniteSource

open Lean
run_meta do
  let info ← getConstInfo `solution
  let expected := Lean.mkConst `AbcAdaptation.Tripod.LegendreFiniteLowerBound
  unless ← Lean.Meta.isDefEq info.type expected do throwError "Exact original target type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile ".local/adaptation/legendre-finite-sourceproof-20261114/solution-legendreFiniteLowerBound-type.json" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr info.type).pretty),("axioms",toJson (axs.map toString))]))
