import Definitions.Def_TripodFermatComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_heightNormalization
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_liftDifferent
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_canonicalEstimate

set_option autoImplicit false

theorem solution (hII : AbcAdaptation.Tripod.StatementII) :
    AbcAdaptation.Tripod.StatementI :=
  AbcAdaptation.Tripod.statementI_of_fermat_children
    AbcAdaptation.Tripod.Fermat.heightNormalization
    AbcAdaptation.Tripod.Fermat.liftDifferent
    AbcAdaptation.Tripod.Fermat.canonicalEstimate
    hII
