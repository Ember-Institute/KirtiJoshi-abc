/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path: Iut/Tripod/CurveFacts.lean (curveInputs.dmod_le field assignment)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_DmodBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField

/-- Exact dmod_le field of the actual-provider source curveInputs constructor. -/
theorem curveInputs_dmod_le (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    Module.finrank ℚ ↥(fieldOfModuli (P.curve x).F (P.curve x).E) ≤ d :=
  (dmod_le x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)).trans hx.2

end AbcAdaptation.Tripod
