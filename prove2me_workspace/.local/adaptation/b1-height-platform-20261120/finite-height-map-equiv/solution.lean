/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Sources: Iut/Cor312/ThetaData/GalCompletion.lean, Iut/Tripod/TwoAdic.lean, and Iut/Tripod/Height.lean.
-/
import Definitions.Def_TripodCanonicalHighHeightInputs
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FinitePlaceMapEquiv

set_option autoImplicit false

open AbcAdaptation.Tripod (finHeight)
open NumberField

open AbcAdaptation.Reference.Iut

theorem solution {T : Type*} [Field T] [NumberField T]
    {T' : Type*} [Field T'] [NumberField T'] (e : T ≃+* T') (y : T) :
    finHeight (e y) = finHeight y := by
  unfold finHeight
  rw [← finsum_comp_equiv (FinitePlace.mapEquiv e)]
  refine finsum_congr fun v => ?_
  rw [FinitePlace.mapEquiv_apply, RingEquiv.symm_apply_apply]
