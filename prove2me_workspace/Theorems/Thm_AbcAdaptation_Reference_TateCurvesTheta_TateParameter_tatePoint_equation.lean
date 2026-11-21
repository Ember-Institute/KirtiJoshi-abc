/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/

import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_PointMap

set_option autoImplicit false

open AbcAdaptation.Reference.TateCurvesTheta
open scoped Classical

theorem AbcAdaptation.Reference.TateCurvesTheta.TateParameter.tatePoint_equation
    {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (t : TateParameter k) (h12 : (12 : k) ≠ 0) :
    t.TatePointEquation := by
  sorry
