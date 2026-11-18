/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path: Iut/Tripod/CurveFacts.lean (curveInputs.deg_le and curveInputs.logDiff_eq)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_DifferentDegree
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

/-- Degree bound for the curve field in the degree locus of the source constructor. -/
theorem curveInputs_deg_le (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (hdeg3 : ∀ x : Pt, TorsionDegreeBound x.1 3)
    (hdeg5 : ∀ x : Pt, TorsionDegreeBound x.1 5)
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    Module.finrank ℚ (P.curve x).F ≤ 552960 * d :=
  (deg_le x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1) (hdeg3 x) (hdeg5 x)).trans
    (Nat.mul_le_mul_left _ hx.2)

/-- Normalized different-degree identity for the curve used by the source constructor. -/
theorem curveInputs_logDiff_eq (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (x : tripodTheory.Pt tripodTheory.tripod)
    (_hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    tripodTheory.logDiff tripodTheory.tripod x =
      logDifferentDeg ↥(tripodalFieldOf (P.curve x).F (P.curve x).E) :=
  logDiff_eq x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)

end AbcAdaptation.Tripod
