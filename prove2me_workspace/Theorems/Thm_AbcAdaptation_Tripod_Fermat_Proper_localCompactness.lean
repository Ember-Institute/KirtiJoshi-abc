/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Solutions.Source_FermatLocalCompactness

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem localCompactness {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : LocalCompactness M := by
  exact Source.localCompactness_source M hRF

end AbcAdaptation.Tripod.Fermat.Proper
