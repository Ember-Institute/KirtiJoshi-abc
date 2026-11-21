/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Mathlib.NumberTheory.RamificationInertia.Valuation

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
