import Theorems.Thm_AbcAdaptation_classicalInt

set_option autoImplicit false

theorem solution : AbcAdaptation.ClassicalABC :=
  AbcAdaptation.classicalABC_of_int AbcAdaptation.classicalInt
