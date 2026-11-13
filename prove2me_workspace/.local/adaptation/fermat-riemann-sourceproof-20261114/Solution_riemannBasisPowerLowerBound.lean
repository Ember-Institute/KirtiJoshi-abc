import Definitions.Def_FermatRiemannBasisPowers

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- Actual powers of u times the actual functionBasis give the exact count. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M)
    (hFinite : ∀ A : Divisor M, FiniteDimensional ℚ (riemannRochSpace M hDVR A))
    (l : ℕ) :
    (l + 1) * N ≤ riemannEll M hDVR
      (l • functionPoleDivisor M hDVR M.u + basisPoleCorrection M hDVR) :=
  RiemannBasisPower.lowerBound M hDVR hFinite l
