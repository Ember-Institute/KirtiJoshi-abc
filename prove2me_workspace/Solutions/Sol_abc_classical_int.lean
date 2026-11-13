import Theorems.Thm_AbcAdaptation_rationalHeight

set_option autoImplicit false

theorem solution : AbcAdaptation.ClassicalABCInt :=
  AbcAdaptation.classicalABCInt_of_rationalABCHeight AbcAdaptation.rationalHeight
