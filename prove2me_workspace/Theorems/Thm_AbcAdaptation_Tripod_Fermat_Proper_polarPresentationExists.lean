/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors, The Belyi project contributors
-/
import Definitions.Def_FermatRiemannComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochFiniteDimensional
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochDimensionUpperBound
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochEventuallyLinear

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement for the existing child. The original signature
is retained; the concrete model already proves the residue-finite input. -/
theorem polarPresentationExists {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M) (D : Divisor M) :
    Nonempty (PolarPresentation M hDVR D) :=
  polarPresentation_of_riemannChildren M hDVR
    (riemannRochFiniteDimensional M hDVR)
    (riemannRochDimensionUpperBound M hDVR)
    (riemannRochEventuallyLinear M hDVR) D

end AbcAdaptation.Tripod.Fermat.Proper
