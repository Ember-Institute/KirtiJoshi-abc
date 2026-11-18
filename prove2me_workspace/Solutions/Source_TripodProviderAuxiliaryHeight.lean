/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Exact normalization consumers of Iut/Tripod/Height.lean:603.
Uncompiled integration draft, no additional mathematical hypotheses.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization
import Definitions.Def_TripodCanonicalHighHeightInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- The actual provider/Tate height agrees with the already fixed canonical expression. -/
theorem providerHeight_eq_auxiliaryHeight (P : CurveProviders) (x : Pt) :
    P.h x = auxiliaryHeight x :=
  h_eq_finHeight_div P x

/-- Function equality for the fixed source/local height normalization. -/
theorem providerHeight_eq_auxiliaryHeight_function (P : CurveProviders) :
    P.h = auxiliaryHeight :=
  funext (providerHeight_eq_auxiliaryHeight P)

/-- The source's exact one-sixth coefficient needs no further normalization. -/
theorem providerHeight_one_sixth_eq_auxiliaryHeight (P : CurveProviders) (x : Pt) :
    (1 / 6 : ℝ) * P.h x = auxiliaryHeight x / 6 := by
  rw [providerHeight_eq_auxiliaryHeight]
  ring

end AbcAdaptation.Tripod
