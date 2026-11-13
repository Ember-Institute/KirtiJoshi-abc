import Definitions.Def_FermatCanonicalCoordinatePoleComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_coordinatePoleMultiplicity_eq

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- The original actual adjunction input and the precise coordinate-pole
child yield the canonical degree. The Fermat pole child remains Open. -/
theorem solution {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hN : 3 < N) (hRF : ResiduesFinite M)
    (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR)
    (J : PlaneAdjunctionData M hDVR K H) :
    divisorDegree M K.D = planeCanonicalDegree N :=
  canonicalDegree_of_coordinatePoles_and_actualAdjunction M hDVR hN
    (coordinatePoleMultiplicity_eq M hDVR (by omega)) K H J
