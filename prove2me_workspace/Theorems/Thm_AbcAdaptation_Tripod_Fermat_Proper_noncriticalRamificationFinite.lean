/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatNoncriticalFunctions

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: a nonconstant actual function is ramified at finitely many places.
Source: CurveField/NoncriticalFinite.lean:181-188. At regular ramified
places the actual derivation d/dψ does not preserve the local ring.
Finite chart generators make its failure locus finite; poles are finite. -/
theorem noncriticalRamificationFinite {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | 1 < ramIdx M hDVR ψ P}.Finite := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
