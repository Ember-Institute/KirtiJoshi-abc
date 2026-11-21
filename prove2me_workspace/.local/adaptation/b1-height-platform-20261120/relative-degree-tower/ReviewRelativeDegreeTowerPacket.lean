import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Mathlib.NumberTheory.RamificationInertia.Valuation
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

section RelativeValuation

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The ramification index `e(v/w)` of `v` over `w`. -/
noncomputable abbrev relRamIdx (v : FinitePlace K) (w : FinitePlace k) : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx' v.maximalIdeal.asIdeal

/-- The residue degree `f(v/w)` of `v` over `w`. -/
noncomputable abbrev relInertDeg (v : FinitePlace K) (w : FinitePlace k) : ℕ :=
  w.maximalIdeal.asIdeal.inertiaDeg' v.maximalIdeal.asIdeal

section Transfer
variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

/-- The ramification index of `w` over `v` is nonzero. -/
lemma ramificationIdx'_ne_zero :
    v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal ≠ 0 := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.maximalIdeal.ne_bot

/-- `w(x) = v(x)^e` for `x ∈ k`, where `e` is the ramification index of `w` over `v`. -/
lemma valuation_algebraMap_eq_pow (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) =
      v.maximalIdeal.valuation k x ^
        v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact (valuation_liesOver K v.maximalIdeal w.maximalIdeal x).symm

end Transfer

section Nonzero
variable {v : FinitePlace K} {w : FinitePlace k} (hvw : FinitePlace.LiesOver v w)
include hvw

/-- The ramification index `e(v/w)` is nonzero. -/
lemma relRamIdx_ne_zero : relRamIdx v w ≠ 0 := ramificationIdx'_ne_zero hvw

end Nonzero

end AbcAdaptation.Tripod

end RelativeValuation

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

section RelativeDegreeTower

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]


section Tower
variable {v : FinitePlace K} {w : FinitePlace k} (hvw : FinitePlace.LiesOver v w)
include hvw

/-- The prime of `ℤ` below `v` is the prime below `w`. -/
lemma under_int_eq_under_int : v.maximalIdeal.asIdeal.under ℤ = w.maximalIdeal.asIdeal.under ℤ := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  rw [← Ideal.under_under (B := 𝓞 k) v.maximalIdeal.asIdeal,
    ← Ideal.over_def v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal]

/-- Places over each other have the same residue characteristic. -/
lemma residueChar_eq_of_liesOver : residueChar v = residueChar w := by
  have h := under_int_eq_under_int hvw
  rw [under_int_eq, under_int_eq, Ideal.span_singleton_eq_span_singleton] at h
  have h' := Int.natAbs_eq_iff_associated.mpr h
  simpa using h'

/-- `e_v = e_w · e(v/w)`. -/
lemma ramIdx_eq_mul : ramIdx K v = ramIdx k w * relRamIdx v w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  have hp : v.maximalIdeal.asIdeal.under ℤ ≠ ⊥ := under_int_ne_bot v
  haveI : w.maximalIdeal.asIdeal.LiesOver (v.maximalIdeal.asIdeal.under ℤ) :=
    Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
  have h1 : ramIdx K v = (v.maximalIdeal.asIdeal.under ℤ).ramificationIdx' v.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx _ v.maximalIdeal.asIdeal hp).symm
  have h2 : ramIdx k w =
      (v.maximalIdeal.asIdeal.under ℤ).ramificationIdx' w.maximalIdeal.asIdeal := by
    have := (Ideal.ramificationIdx'_eq_ramificationIdx (w.maximalIdeal.asIdeal.under ℤ)
      w.maximalIdeal.asIdeal (under_int_ne_bot w)).symm
    rw [under_int_eq_under_int hvw]
    exact this
  rw [h1, h2]
  exact Ideal.ramificationIdx'_algebra_tower' _ w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal

/-- `f_v = f_w · f(v/w)`. -/
lemma inertDeg_eq_mul : inertDeg K v = inertDeg k w * relInertDeg v w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  haveI : w.maximalIdeal.asIdeal.LiesOver (v.maximalIdeal.asIdeal.under ℤ) :=
    Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
  haveI : (v.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal v
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  have h1 : inertDeg K v = (v.maximalIdeal.asIdeal.under ℤ).inertiaDeg' v.maximalIdeal.asIdeal :=
    (Ideal.inertiaDeg'_eq_inertiaDeg _ v.maximalIdeal.asIdeal).symm
  have h2 : inertDeg k w = (v.maximalIdeal.asIdeal.under ℤ).inertiaDeg' w.maximalIdeal.asIdeal := by
    haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
    have := (Ideal.inertiaDeg'_eq_inertiaDeg (w.maximalIdeal.asIdeal.under ℤ)
      w.maximalIdeal.asIdeal).symm
    rw [under_int_eq_under_int hvw]
    exact this
  rw [h1, h2]
  exact Ideal.inertiaDeg'_algebra_tower _ w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal

/-- `[K_v : ℚ_p] = [k_w : ℚ_p] · e(v/w) f(v/w)`. -/
lemma localDeg_eq_mul : localDeg K v = localDeg k w * (relRamIdx v w * relInertDeg v w) := by
  unfold localDeg
  rw [ramIdx_eq_mul hvw, inertDeg_eq_mul hvw]
  ring

end Tower

/-- The local degree `e(w/v) f(w/v)` of `w` over `v`. -/
noncomputable abbrev relLocalDeg (w : FinitePlace K) (v : FinitePlace k) : ℕ :=
  relRamIdx w v * relInertDeg w v

lemma relLocalDeg_ne_zero {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : relLocalDeg w v ≠ 0 := by
  have h := inertDeg_eq_mul hwv
  have hpos := inertDeg_pos' w
  refine mul_ne_zero (relRamIdx_ne_zero hwv) fun h0 => ?_
  rw [h, h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

end AbcAdaptation.Tripod

end RelativeDegreeTower

#print axioms AbcAdaptation.Tripod.under_int_eq_under_int
#print axioms AbcAdaptation.Tripod.residueChar_eq_of_liesOver
#print axioms AbcAdaptation.Tripod.ramIdx_eq_mul
#print axioms AbcAdaptation.Tripod.inertDeg_eq_mul
#print axioms AbcAdaptation.Tripod.localDeg_eq_mul
#print axioms AbcAdaptation.Tripod.relLocalDeg
#print axioms AbcAdaptation.Tripod.relLocalDeg_ne_zero
