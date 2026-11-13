/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveField/NoncriticalFinite.lean exists_derivAlong_notMem.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 97605e681191f8a923c7de80df284e327550f708a884b5deb135e469b6a2bbf8.
-/
import Definitions.Def_FermatNoncriticalFunctions
import Definitions.Def_FermatCurveDerivationBasic

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: source local obstruction. At a regular ramified place, the
actual derivative with respect to ψ fails to preserve the actual local ring.
Both local rings and ramification indices are those of the existing model;
no derivation or derivation law is supplied as a hypothesis. -/
theorem noncriticalRegularRamifiedDerivNotMem {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (hψP : ψ ∈ P.1) (hram : 1 < ramIdx M hDVR ψ P) :
    ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1 := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
