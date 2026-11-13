import Definitions.Def_TripodStatementIIComposition
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
import Theorems.Thm_AbcAdaptation_Tripod_highHeightEstimate

set_option autoImplicit false

theorem solution : AbcAdaptation.Tripod.StatementII :=
  AbcAdaptation.Tripod.statementII_of_children
    AbcAdaptation.Tripod.boundedDegreeFiniteness
    AbcAdaptation.Tripod.highHeightEstimate
