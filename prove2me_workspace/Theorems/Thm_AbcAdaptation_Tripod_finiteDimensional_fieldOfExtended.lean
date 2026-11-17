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
import Theorems.Thm_AbcAdaptation_Tripod_torsionCoords_finite

namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

/-- `F_λ` is a finite extension of `ℚ` when the `3`- and `5`-torsion of `E_λ(ℚ̄)` are
finite. -/
theorem finiteDimensional_fieldOfExtended {l : Qbar} (h3 : TorsionFinite l 3) (h5 : TorsionFinite l 5) :
    FiniteDimensional ℚ (fieldOf' l) := by
  have hfin : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} ∪ torsionCoords l 3 ∪
      torsionCoords l 5).Finite :=
    ((Set.toFinite _).union (torsionCoords_finite h3)).union (torsionCoords_finite h5)
  haveI := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ ↦ isIntegral x

end AbcAdaptation.Tripod
