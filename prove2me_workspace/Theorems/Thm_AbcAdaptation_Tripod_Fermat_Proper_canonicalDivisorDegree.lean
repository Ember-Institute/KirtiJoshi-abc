/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Composition of source divisor-degree laws at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8 with one explicit Open Fermat
coordinate-pole child and the original actual adjunction input.
The Open child's proof is not supplied by the pinned source.
-/
import Definitions.Def_FermatCanonicalCoordinatePoleComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_coordinatePoleMultiplicity_eq

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The original actual adjunction input and the precise coordinate-pole
child yield the canonical degree. The Fermat pole child remains Open. -/
theorem canonicalDivisorDegree {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hN : 3 < N) (hRF : ResiduesFinite M)
    (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR)
    (J : PlaneAdjunctionData M hDVR K H) :
    divisorDegree M K.D = planeCanonicalDegree N :=
  canonicalDegree_of_coordinatePoles_and_actualAdjunction M hDVR hN
    (coordinatePoleMultiplicity_eq M hDVR (by omega)) K H J

end AbcAdaptation.Tripod.Fermat.Proper
