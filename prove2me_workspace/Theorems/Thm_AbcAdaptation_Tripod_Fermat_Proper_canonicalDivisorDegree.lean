/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN NEW SPECIALIZATION: the genuine canonical degree of the Fermat
function field. Its proof must compute deg H=N, use the degree-zero theorem
for the principal divisor of J.r, and sum J.coefficient. The fixed number
planeCanonicalDegree alone is not a proof of this equality. -/
theorem canonicalDivisorDegree {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hN : 3 < N) (hRF : ResiduesFinite M)
    (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR)
    (J : PlaneAdjunctionData M hDVR K H) :
    divisorDegree M K.D = planeCanonicalDegree N := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
