/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveField/NoncriticalElem.lean applyK_spec.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 962260751d00333f25cfcd803626193c053d0a982fb6756823de1cc325f4b783.
-/
import Definitions.Def_FermatNoncriticalFunctions

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the actual single-elementary-map composition step from the source.
The map is a rational Möbius transformation with nonzero determinant or a
positive-degree rational polynomial. Every actual residue embedding is kept. -/
theorem noncriticalElementaryCompositionRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : NoncriticalP1.ElemMap) :
    Transcendental ℚ (NoncriticalP1.applyK h ψ) ∧
    noncriticalValue M x (NoncriticalP1.applyK h ψ) = h.apply (noncriticalValue M x ψ) ∧
    ramIdx M hDVR (NoncriticalP1.applyK h ψ) x.P =
      ramIdx M hDVR ψ x.P * (h.ramIdx (noncriticalValue M x ψ) : ℤ) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
