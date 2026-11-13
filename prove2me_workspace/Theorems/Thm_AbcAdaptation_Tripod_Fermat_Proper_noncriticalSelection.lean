/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatProperCarrier

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem noncriticalSelection {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : NoncriticalSelection M hDVR := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
