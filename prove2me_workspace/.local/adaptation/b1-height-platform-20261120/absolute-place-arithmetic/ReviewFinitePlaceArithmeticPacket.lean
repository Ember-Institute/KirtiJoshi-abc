import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

section InertiaDegree

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField

noncomputable def inertDeg (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ

end AbcAdaptation.Tripod

end InertiaDegree

section FinitePlaceArithmetic

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

noncomputable def ramIdx (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  Ideal.ramificationIdx w.maximalIdeal.asIdeal ℤ

noncomputable def localDeg (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  ramIdx K w * inertDeg K w

noncomputable abbrev completionAt (K : Type*) [Field K] [NumberField K]
    (w : FinitePlace K) := w.maximalIdeal.adicCompletion K

section
variable {k : Type*} [Field k] [NumberField k]
lemma residueChar_prime (w : FinitePlace k) : (AbcAdaptation.Reference.Iut.residueChar w).Prime := by
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
    v.maximalIdeal.asIdeal.under ℤ = Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)} := by
  set P := v.maximalIdeal.asIdeal
  have hp : (AbcAdaptation.Reference.Iut.residueChar v).Prime := residueChar_prime v
  haveI : CharP (𝓞 K ⧸ P) (AbcAdaptation.Reference.Iut.residueChar v) := ringChar.charP _
  have hmem : (AbcAdaptation.Reference.Iut.residueChar v : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.natCast_mem_of_charP_quotient (AbcAdaptation.Reference.Iut.residueChar v) P
  have hle : Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  haveI hprime : (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hmax : (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}).IsMaximal :=
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
  have hp : (AbcAdaptation.Reference.Iut.residueChar v).Prime := residueChar_prime v
  rw [under_int_eq]
  haveI : (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  exact IsPrime.to_maximal_ideal (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero)

/-- The prime of a finite place lies over `(p)`, `p` its residue characteristic. -/
lemma liesOver_span_residueChar (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.LiesOver (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}) :=
  ⟨(under_int_eq v).symm⟩

/-- `N(𝔭_v) = p^{f_v}`. -/
lemma absNorm_eq_pow_residueChar (v : FinitePlace K) :
    Ideal.absNorm v.maximalIdeal.asIdeal = AbcAdaptation.Reference.Iut.residueChar v ^ inertDeg K v := by
  haveI := liesOver_span_residueChar v
  exact (Ideal.pow_inertiaDeg (AbcAdaptation.Reference.Iut.residueChar v) v.maximalIdeal.asIdeal).symm

/-- `f_v > 0`. -/
lemma inertDeg_pos' (v : FinitePlace K) : 0 < inertDeg K v :=
  Ideal.inertiaDeg_pos v.maximalIdeal.asIdeal ℤ

/-- `e_v > 0`. -/
lemma ramIdx_pos' (v : FinitePlace K) : 0 < ramIdx K v :=
  Ideal.ramificationIdx_pos v.maximalIdeal.asIdeal ℤ

/-- The norm of an element of valuation `exp m` is `(p^{f_v})^m`. -/
lemma norm_eq_zpow_of_valued (v : FinitePlace K) (x : completionAt K v) (m : ℤ)
    (hx : Valued.v x = exp m) :
    ‖x‖ = ((AbcAdaptation.Reference.Iut.residueChar v : ℝ) ^ inertDeg K v) ^ m := by
  rw [FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  have h : (WithZero.unzero (exp_ne_zero (a := m))).toAdd = m := rfl
  rw [h, NNReal.coe_zpow, NNReal.coe_natCast, absNorm_eq_pow_residueChar, Nat.cast_pow]
end

theorem log_apply_eq {T : Type*} [Field T] [NumberField T] (𝔭 : FinitePlace T) {y : T}
    (hy : y ≠ 0) :
    Real.log (𝔭 y) = ((log (𝔭.maximalIdeal.valuation T y) : ℤ) : ℝ) *
      (inertDeg T 𝔭 * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭)) := by
  have hv : 𝔭.maximalIdeal.valuation T y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  rw [← FinitePlace.norm_embedding_eq,
    norm_eq_zpow_of_valued 𝔭 _ (log (𝔭.maximalIdeal.valuation T y)) (by
      rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', exp_log hv]),
    Real.log_zpow, Real.log_pow]

end AbcAdaptation.Tripod

end FinitePlaceArithmetic

#print axioms AbcAdaptation.Tripod.log_apply_eq
