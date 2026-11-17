/-
Adaptation provenance: accepted Iut source AST spans; only bound identifier changes are recorded.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Tripod/CurveOf.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData

namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

theorem mem_fieldOfExtended_self (l : Qbar) : l ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

end AbcAdaptation.Tripod
