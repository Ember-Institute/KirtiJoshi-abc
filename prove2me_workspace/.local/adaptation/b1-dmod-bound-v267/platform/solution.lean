/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path: Iut/Tripod/CurveFacts.lean
Selected declarations for the field of moduli and its degree bound.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut
open WeierstrassCurve NumberField Polynomial
open scoped IntermediateField

section Curve

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

private theorem fieldOfModuli_le :
    fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E ≤ ℚ⟮genC x h3 h5⟯ :=
  IntermediateField.adjoin_simple_le_iff.mpr (j_mem_adjoin x h3 h5)

private theorem isIntegral_genC : IsIntegral ℚ (genC x h3 h5) :=
  Algebra.IsIntegral.isIntegral _

private theorem finrank_adjoin_genC : Module.finrank ℚ ℚ⟮genC x h3 h5⟯ = deg x.1 := by
  rw [(adjoinGenCEquiv x h3 h5).toLinearEquiv.finrank_eq, deg_eq_finrank]

theorem solution :
    Module.finrank ℚ ↥(fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E) ≤ deg x.1 := by
  haveI : FiniteDimensional ℚ ℚ⟮genC x h3 h5⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_genC x h3 h5)
  rw [← finrank_adjoin_genC x h3 h5]
  exact IntermediateField.finrank_le_of_le_right (fieldOfModuli_le x h3 h5)

end Curve
