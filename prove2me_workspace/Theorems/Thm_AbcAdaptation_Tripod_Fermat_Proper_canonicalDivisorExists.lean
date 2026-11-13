/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: finite support of the actual coefficients of div(du).
Source: pinned Belyi/CurveField/Canonical.lean:42-83, using the finite
ramification locus and finite set of poles of the transcendental coordinate u. -/
theorem canonicalDivisorExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : Nonempty (CanonicalDivisorData M hDVR) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
