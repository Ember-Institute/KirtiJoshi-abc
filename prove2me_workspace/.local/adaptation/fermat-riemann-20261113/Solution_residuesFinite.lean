import Definitions.Def_FermatCurveFieldResidue

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

theorem solution {N : ℕ} (M : Model N) : ResiduesFinite M :=
  model_residuesFinite M
