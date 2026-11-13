import Definitions.Def_FermatCurveFieldResidue

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

theorem solution {N : ℕ} (M : Model N) : PlacesDiscrete M :=
  model_placesDiscrete M
