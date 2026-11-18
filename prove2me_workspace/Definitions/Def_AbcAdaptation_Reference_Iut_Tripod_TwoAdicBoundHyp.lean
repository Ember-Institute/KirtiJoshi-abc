/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (K : CompactlyBounded)

def TwoAdicBoundHyp (B : ℝ) : Prop := ∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B

end AbcAdaptation.Tripod
