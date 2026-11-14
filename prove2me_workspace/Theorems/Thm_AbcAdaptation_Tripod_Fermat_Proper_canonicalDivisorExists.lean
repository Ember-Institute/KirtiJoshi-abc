/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent coefficient-support adaptation of Belyi/CurveField/Canonical.lean
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, using the actual fixed Fermat u.
The finite ramification premise is the exact specialization of
Belyi/CurveField/RamIdx.lean finite_setOf_one_lt_ramIdx.
-/
import Solutions.Source_FermatCanonicalFiniteRamification
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRamificationFinite

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The original parent uses the already proved actual finite ramification locus.
Its name, all original hypotheses, and its exact output data are retained. -/
theorem canonicalDivisorExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : Nonempty (CanonicalDivisorData M hDVR) :=
  canonicalDivisorExists_of_finiteCoordinateRamification
    (fun M hDVR _ => noncriticalRamificationFinite M hDVR M.u M.transcendental_u)
    M hDVR hRF

end AbcAdaptation.Tripod.Fermat.Proper
