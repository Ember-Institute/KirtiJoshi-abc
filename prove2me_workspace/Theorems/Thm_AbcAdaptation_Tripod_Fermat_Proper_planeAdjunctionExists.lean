/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN NEW SPECIALIZATION: div(du) ~ (N-3)[W=0] on the smooth plane
Fermat curve, through the divisor of an actual rational function.
This needs the local Fermat order calculation or algebraic adjunction;
the generic pinned Genl Kummer construction does not establish it alone. -/
theorem planeAdjunctionExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hN : 3 < N) (hRF : ResiduesFinite M)
    (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR) :
    Nonempty (PlaneAdjunctionData M hDVR K H) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
