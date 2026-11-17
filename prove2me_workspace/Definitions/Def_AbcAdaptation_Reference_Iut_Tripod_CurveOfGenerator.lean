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
import Theorems.Thm_AbcAdaptation_Tripod_mem_fieldOfExtended_self

namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

/-- The element `λ` of `F_λ`. -/
noncomputable def gen' (l : Qbar) : fieldOf' l := ⟨l, mem_fieldOfExtended_self l⟩

end AbcAdaptation.Tripod
