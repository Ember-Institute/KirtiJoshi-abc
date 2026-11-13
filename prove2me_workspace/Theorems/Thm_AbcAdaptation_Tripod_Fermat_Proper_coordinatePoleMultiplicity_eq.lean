/-
Copyright (c) 2026 The abc project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The abc project contributors

NEW OPEN Fermat specialization. No proof of this identity is attributed to
Belyi at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8 or to Heights.
The definitions of the fixed Model and actual normalized pole multiplicities
remain those independently adapted from the pinned source.
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN NEW SPECIALIZATION: the fixed Fermat coordinates have the same
actual pole multiplicity at every proper place, including infinity.
This includes regular places and all zero-coordinate cases.
The assertion has no arbitrary degree, order function, or law parameter. -/
theorem coordinatePoleMultiplicity_eq {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (hN : 0 < N) (P : Place M.K) :
    poleMultiplicity M hDVR M.u P = poleMultiplicity M hDVR M.v P := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
