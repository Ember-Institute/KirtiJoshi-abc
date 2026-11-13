/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the union of the actual pole sets of u and v is finite.
Source: pinned Belyi/CurveField/Place.lean finite_setOf_notMem and
Heights/Curve/TupleHeight.lean, the divisor A_[1,u,v]. -/
theorem infinityDivisorExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : Nonempty (InfinityDivisorData M hDVR) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
