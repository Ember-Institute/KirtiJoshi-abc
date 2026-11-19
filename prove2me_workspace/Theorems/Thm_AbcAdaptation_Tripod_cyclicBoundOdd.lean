/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (cyclicBoundOdd)
-/
import Solutions.Source_TripodCyclicBoundOdd
import Theorems.Thm_AbcAdaptation_Tripod_legendre_torsion_x_le

set_option autoImplicit false

namespace AbcAdaptation.Tripod

theorem cyclicBoundOdd (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    CyclicBoundOddHyp P K d (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := by
  sorry

end AbcAdaptation.Tripod
