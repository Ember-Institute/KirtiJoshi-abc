/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicLocal.lean (comap_bcKR_eq_graphLineAt)
               and Iut/Tripod/CyclicBound.lean (isGraphPlace_of_not_dvd)
-/
import Solutions.Source_TripodCyclicLocal

set_option autoImplicit false

namespace AbcAdaptation.Tripod

theorem cyclicLocalGraphLine (P : CurveProviders) : CyclicLocalGraphLineHyp P :=
  cyclicLocalGraphLine_from_source P

end AbcAdaptation.Tripod
