/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatNoncriticalFunctions

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement with the original signature. Finite support holds
for every actual φ, so the existing hRF and hφ parameters remain compatible. -/
theorem cuspsFinite {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ) :
    (cusps M hDVR φ).Finite :=
  model_cuspsFinite M hDVR φ

end AbcAdaptation.Tripod.Fermat.Proper
