/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:714-719; exact original parent LegendreFiniteUpperBound.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/
import Definitions.Def_TripodLegendreHeightComparisonInputs
import Solutions.Source_TripodFiniteHeightSupport
import Solutions.Source_TripodLegendreFinitePlaceBounds

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

theorem legendreFiniteUpperBound : LegendreFiniteUpperBound := by
  intro x
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  exact Finset.sum_le_sum fun v _ => posLog_legendreJ_le v (gen_ne_zero x.2.1) (gen_ne_one x)

end AbcAdaptation.Tripod
