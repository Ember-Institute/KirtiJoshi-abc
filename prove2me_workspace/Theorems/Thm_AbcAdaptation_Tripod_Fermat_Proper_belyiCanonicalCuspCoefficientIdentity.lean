/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

DRAFT: exact open source obligation from Belyi/CurveField/BelyiRelation.lean:85,
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The differential coefficient of dφ plus the actual reduced cusp
coefficient equals the pole coefficient plus the order of φ(φ-1).
This is an equality at all proper places, including every pole. The finite
sum uses the supplied cusp-finiteness proof without selecting another divisor. -/
theorem belyiCanonicalCuspCoefficientIdentity {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    ∀ P : Place M.K,
      (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
        else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1)) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
