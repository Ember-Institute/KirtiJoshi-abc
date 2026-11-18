/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by the current reference adaptation:
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
Source: Iut/Tripod/CurveFacts.lean:402.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
import Definitions.Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference

variable (P : CurveProviders) (K : CompactlyBounded)

/-- **IUT IV, Corollary 2.2(i)** ([GenEll], Proposition 3.4): `(1/6)·log(q_∀) ≈ ht_{𝒪(1)}`
on a compactly bounded subset. -/
def LegendreHeightHyp : Prop := ((1 / 6 : ℝ) • P.h) ≈[K.set] htCan

end AbcAdaptation.Tripod
