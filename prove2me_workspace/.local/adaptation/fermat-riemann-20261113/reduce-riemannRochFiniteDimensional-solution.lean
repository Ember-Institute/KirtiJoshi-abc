import Definitions.Def_FermatRiemannLocalDimension
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_functionZeroPoleDegrees

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement. The local residue map and its kernel are proved
in Definitions; the only remaining mathematical input is the actual
zero/pole fiber degree theorem, which gives principal degree zero. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (A : Divisor M) :
    FiniteDimensional ℚ (riemannRochSpace M hDVR A) := by
  letI : IsCurveField M.K := M.isCurveField
  exact RiemannDimension.finiteDimensional_L M hDVR
    (principalDegreeZero_of_zeroPoleDegrees M hDVR (functionZeroPoleDegrees M hDVR)) A
