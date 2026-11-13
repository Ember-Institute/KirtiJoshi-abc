/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcTripod
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false

namespace AbcAdaptation.Tripod

theorem radicalConductorProjection : RadicalConductorProjection := by
  intro q h0 h1
  rw [logCond_eq_sum]
  sorry

end AbcAdaptation.Tripod
