/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatRiemannLocalDimension
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_functionZeroPoleDegrees

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement. Multiplication by an actual nonzero function
gives the linear equivalence; the source residue-map dimension estimate
gives this exact bound with the actual ell(0), not an assumed value 1. -/
theorem riemannRochDimensionUpperBound {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (A : Divisor M) :
    (riemannEll M hDVR A : ℤ) ≤
      max 0 (divisorDegree M A + (riemannEll M hDVR 0 : ℤ)) := by
  letI : IsCurveField M.K := M.isCurveField
  exact RiemannDimension.ell_le_max M hDVR
    (principalDegreeZero_of_zeroPoleDegrees M hDVR (functionZeroPoleDegrees M hDVR)) A

end AbcAdaptation.Tripod.Fermat.Proper
