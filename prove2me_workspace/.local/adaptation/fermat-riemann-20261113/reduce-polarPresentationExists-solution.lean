import Definitions.Def_FermatRiemannComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochFiniteDimensional
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochDimensionUpperBound
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochEventuallyLinear

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement for the existing child. The original signature
is retained; the concrete model already proves the residue-finite input. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M) (D : Divisor M) :
    Nonempty (PolarPresentation M hDVR D) :=
  polarPresentation_of_riemannChildren M hDVR
    (riemannRochFiniteDimensional M hDVR)
    (riemannRochDimensionUpperBound M hDVR)
    (riemannRochEventuallyLinear M hDVR) D
