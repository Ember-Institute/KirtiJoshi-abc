import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut
open WeierstrassCurve NumberField Polynomial
open scoped IntermediateField

theorem AbcAdaptation.Tripod.dmod_le (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    Module.finrank ℚ ↥(fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E) ≤ deg x.1 := by sorry
