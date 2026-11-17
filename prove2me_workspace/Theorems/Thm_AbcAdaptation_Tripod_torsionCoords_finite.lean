/-
Adaptation provenance: original accepted Iut source AST command spans.
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

theorem torsionCoords_finite {l : Qbar} {n : ℕ} (h : TorsionFinite l n) :
    (torsionCoords l n).Finite :=
  h.biUnion fun P _ ↦ by
    cases P with
    | zero => exact Set.finite_empty
    | some x y _ => exact (Set.finite_singleton y).insert x

end AbcAdaptation.Tripod
