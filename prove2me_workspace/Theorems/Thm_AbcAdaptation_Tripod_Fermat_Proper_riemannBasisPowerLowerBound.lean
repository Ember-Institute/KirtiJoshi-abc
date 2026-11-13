/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of Belyi/CurveField/Riemann.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannBasisPowers

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Actual powers of u times the actual functionBasis give the exact count. -/
theorem riemannBasisPowerLowerBound {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M)
    (hFinite : ∀ A : Divisor M, FiniteDimensional ℚ (riemannRochSpace M hDVR A))
    (l : ℕ) :
    (l + 1) * N ≤ riemannEll M hDVR
      (l • functionPoleDivisor M hDVR M.u + basisPoleCorrection M hDVR) :=
  RiemannBasisPower.lowerBound M hDVR hFinite l

end AbcAdaptation.Tripod.Fermat.Proper
