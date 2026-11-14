/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

The source proof chain is independently adapted in Source_FermatCoordRingSource
from Belyi/CurveField/CoordRing.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8 and the invocation in
Genl/Curves/BelyiDescent.lean at ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf.
-/
import Solutions.Source_FermatCoordRingSource
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochFiniteDimensional
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochDimensionUpperBound
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochEventuallyLinear

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Finite generation of the actual complement coordinate ring, extending
all three fixed tripod generators. The original signature is preserved. -/
theorem cuspGeneratorsExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    Nonempty (CuspGenerators M hDVR φ hfin) := by
  letI : IsCurveField M.K := M.isCurveField
  exact CuspCoordRingSource.cuspGenerators_of_polarRealization M hDVR
    (largeEffectivePolarRealization_of_riemannChildren M hDVR
      (riemannRochFiniteDimensional M hDVR)
      (riemannRochDimensionUpperBound M hDVR)
      (riemannRochEventuallyLinear M hDVR)) φ hφ.1 hfin

end AbcAdaptation.Tripod.Fermat.Proper
