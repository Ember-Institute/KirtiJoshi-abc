/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveField/NoncriticalFinite.lean finite_setOf_one_lt_ramIdx.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 97605e681191f8a923c7de80df284e327550f708a884b5deb135e469b6a2bbf8.
-/
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- A nonconstant actual function is ramified at finitely many places.
Source combination: every ramified place is a pole or a regular place
where the actual derivative does not preserve the local ring. -/
theorem noncriticalRamificationFinite {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | 1 < ramIdx M hDVR ψ P}.Finite := by
  letI : IsCurveField M.K := M.isCurveField
  refine ((Place.finite_setOf_notMem ψ).union
    (noncriticalDerivativeBadPlacesFinite M ψ hψ)).subset ?_
  intro P hP
  by_cases hψP : ψ ∈ P.1
  · exact Or.inr ⟨hψP, noncriticalRegularRamifiedDerivNotMem M hDVR ψ hψ P hψP hP⟩
  · exact Or.inl hψP

end AbcAdaptation.Tripod.Fermat.Proper
