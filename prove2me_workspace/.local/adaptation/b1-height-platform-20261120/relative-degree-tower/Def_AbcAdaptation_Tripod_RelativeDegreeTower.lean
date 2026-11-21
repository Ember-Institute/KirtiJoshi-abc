/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Definitions.Def_AbcAdaptation_Tripod_RelativeValuation
import Definitions.Def_AbcAdaptation_Tripod_FinitePlaceArithmetic

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
