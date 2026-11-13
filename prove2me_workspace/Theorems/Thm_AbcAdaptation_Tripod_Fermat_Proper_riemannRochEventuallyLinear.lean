/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatRiemannDimensionComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_functionZeroPoleDegrees
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannPolarApproximation
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannBasisPowerLowerBound

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement. Actual fiber degrees, actual approximation, and
the actual basis-power dimension lower bound imply bounded dimension
defect; its attained integer maximum gives eventual equality. -/
theorem riemannRochEventuallyLinear {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) :
    ∃ g0 N0 : ℤ, ∀ A : Divisor M, N0 ≤ divisorDegree M A →
      (riemannEll M hDVR A : ℤ) = divisorDegree M A - g0 := by
  letI : IsCurveField M.K := M.isCurveField
  have hPrincipal := principalDegreeZero_of_zeroPoleDegrees M hDVR
    (functionZeroPoleDegrees M hDVR)
  have hPole := (functionZeroPoleDegrees M hDVR M.u M.transcendental_u).2
  rw [M.degree_u] at hPole
  exact riemannEventuallyLinear_of_degree_approximation_basis M hDVR hPrincipal hPole
    (riemannPolarApproximation M hDVR)
    (riemannBasisPowerLowerBound M hDVR
      (RiemannDimension.finiteDimensional_L M hDVR hPrincipal))

end AbcAdaptation.Tripod.Fermat.Proper
