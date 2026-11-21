import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp

set_option autoImplicit false

open AbcAdaptation.Tripod

theorem AbcAdaptation.Tripod.twoAdicBound (P : CurveProviders) (K : CompactlyBounded) :
    TwoAdicBoundHyp P K (max (4 * K.c) 0) := by sorry
