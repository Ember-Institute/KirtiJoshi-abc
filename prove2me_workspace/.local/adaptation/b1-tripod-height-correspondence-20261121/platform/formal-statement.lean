import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
import Definitions.Def_TripodCanonicalHighHeightInputs

set_option autoImplicit false

open AbcAdaptation.Tripod (CurveProviders Pt finHeight legendreJ gen deg)

theorem AbcAdaptation.Tripod.h_eq_finHeight_div (P : CurveProviders) (x : Pt) : P.h x = finHeight (legendreJ (gen x.1)) / deg x.1 := by sorry
