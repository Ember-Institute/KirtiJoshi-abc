/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableTwo.lean
-/
import Solutions.Source_ReferenceIutStableThreeTorsion
import Solutions.Source_TripodStableOdd
import Solutions.Source_TripodStableTorsionPoints

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField
open scoped Classical

/-- The Legendre curve over its field of definition has stable reduction at every finite place. -/
theorem stable_reduction_curveOf (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) (w : FinitePlace (curveOf x h3 h5).F) :
    HasStableReductionAt (curveOf x h3 h5).E w := by
  by_cases hw : residueChar w = 2
  · have hw3 : AbcAdaptation.Reference.Iut.residueChar w ≠ 3 := by
      change residueChar w ≠ 3
      rw [hw]
      decide
    obtain ⟨P, Q, hP3, hQ3, hP0, hQ0, hQP, hQP'⟩ :=
      independent_three_torsion_curveOf x h3 h5
    exact hasStableReductionAt_of_three_torsion (curveOf x h3 h5).E w hw3 P Q hP3 hQ3
      hP0 hQ0 hQP hQP'
  · exact stable_reduction_of_residueChar_ne_two x h3 h5 w hw

end AbcAdaptation.Tripod
