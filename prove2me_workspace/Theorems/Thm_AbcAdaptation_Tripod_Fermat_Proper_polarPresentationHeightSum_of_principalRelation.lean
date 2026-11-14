/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

DECOMPOSITION DRAFT: the mathematical proof below remains open.
Sources: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1,
Curve/LinearEquiv.lean:74, Curve/DivisorHeight.lean:112,147,
Curve/TupleHeight.lean:249,268 and Absolute/Basic.lean:204.
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- A coefficient identity of actual divisors gives a uniform comparison
for every supplied polar presentation and every full proper algebraic point.
The functionHeight term is projective: it equals zero at poles of f.

Source proof route: take Segre products of the two numerator pair tuples
and the two denominator pair tuples. Compare these products with (1,f)
and the one-entry tuple (1). Apply abs_tupleHeight_sub_sub_le with r⁻¹,
not r, because this statement puts +ord(r) on the divisor side. -/
theorem polarPresentationHeightSum_of_principalRelation {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (D E : Divisor M) (RD : PolarPresentation M hDVR D)
    (RE : PolarPresentation M hDVR E) (f r : M.K) (hr : r ≠ 0)
    (hrel : ∀ P : Place M.K,
      D P + E P = poleMultiplicity M hDVR f P + ord M hDVR P r) :
    ∃ C : ℝ, ∀ x : QbarPoint M.K,
      |divHeight RD x + divHeight RE x - functionHeight M f x| ≤ C := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
