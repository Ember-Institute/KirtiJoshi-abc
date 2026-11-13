/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of pinned source proofs in
Belyi/CurveField/{Point,NoncriticalBasic,NoncriticalElem}.lean and
Belyi/NoncriticalP1/ElemMap.lean. Commit:
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
See source-consumer.json for exact source boundaries and transformations.
-/
import Definitions.Def_FermatNoncriticalElementarySource

set_option autoImplicit false
open Polynomial
namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalBasic.lean ord_aeval_eq. -/
theorem noncriticalPolynomialOrderAtRegularPoint {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : ψ ∈ x.P.1) {g : ℚ[X]} (hg : g ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    x.P.ord (aeval ψ g) = ramIdx M hDVR ψ x.P *
      ((g.map (algebraMap ℚ Tripod.Qbar)).rootMultiplicity (x.eval ψ h) : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
