/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/

import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_PointMap

set_option autoImplicit false

open AbcAdaptation.Reference.TateCurvesTheta
open scoped Classical

theorem AbcAdaptation.Reference.TateCurvesTheta.TateParameter.tatePoint_mul
    {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k] [DecidableEq k]
    (t : TateParameter k) (hmem : t.TatePointEquation)
    (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) (u v : kˣ) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  sorry
