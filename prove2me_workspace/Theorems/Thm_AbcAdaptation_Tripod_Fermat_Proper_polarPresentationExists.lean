/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: Riemann's theorem, not a choice of a free height function.
Source: pinned Belyi/CurveField/Riemann.lean:372. -/
theorem polarPresentationExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) (D : Divisor M) :
    Nonempty (PolarPresentation M hDVR D) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
