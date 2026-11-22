/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/Providers.lean
-/
import Solutions.Source_ReferenceIutCurveArithmeticProved
import Solutions.Source_TripodCurveDegreePrime
import Solutions.Source_TripodProviderRationality
import Solutions.Source_TripodProviderRepresentation
import Solutions.Source_TripodStableReduction

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

/-- The curve providers of the Legendre curves over their fields of definition. -/
noncomputable def tripodProviders : CurveProviders :=
  CurveProviders.ofArithmetic fun x =>
    EllipticCurveData.CurveArithmetic.ofCore _
      (sqrt_neg_one_curveOf x _ _)
      (stable_reduction_curveOf x _ _)
      (six_torsion_rational_curveOf x _ _)
      (galois_deg_prime x _ _)

end AbcAdaptation.Tripod
