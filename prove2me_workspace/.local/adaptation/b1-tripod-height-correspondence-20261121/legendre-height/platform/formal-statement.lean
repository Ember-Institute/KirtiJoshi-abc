import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp

set_option autoImplicit false

open AbcAdaptation.Tripod (CurveProviders CompactlyBounded LegendreHeightHyp)

theorem AbcAdaptation.Tripod.legendreHeight (P : CurveProviders) (K : CompactlyBounded) : LegendreHeightHyp P K := by sorry
