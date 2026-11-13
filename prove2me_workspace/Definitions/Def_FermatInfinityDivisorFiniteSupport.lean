/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent finite-support adaptation of Belyi/CurveField/{ZerosPoles,Divisor}.lean
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The hyperplane coefficient follows the tuple-divisor convention in
Heights/Curve/TupleHeight.lean at 721496ca4c158e511d25d8ccf6bfe8503eda73c1.
-/
import Definitions.Def_FermatFunctionDivisors

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- The exact hyperplane coefficient has support in the union of the existing
finite coordinate supports. No Fermat common-pole identity is used. -/
noncomputable def coordinateInfinityDivisor (M : Model N) (hDVR : PlacesDiscrete M) :
    Divisor M := by
  letI : IsCurveField M.K := M.isCurveField
  exact Finsupp.ofSupportFinite
    (fun P => max (poleMultiplicity M hDVR M.u P) (poleMultiplicity M hDVR M.v P))
    (((Place.finite_setOf_ord_ne_zero M.u).union
      (Place.finite_setOf_ord_ne_zero M.v)).subset fun P hP => by
        simp only [Function.mem_support] at hP
        simp only [Set.mem_union, Set.mem_setOf_eq]
        by_contra h
        push_neg at h
        apply hP
        simp only [poleMultiplicity, ord_eq_placeOrd, h.1, h.2, neg_zero, max_self])

@[simp] theorem coordinateInfinityDivisor_apply (M : Model N) (hDVR : PlacesDiscrete M)
    (P : Place M.K) :
    coordinateInfinityDivisor M hDVR P =
      max (poleMultiplicity M hDVR M.u P) (poleMultiplicity M hDVR M.v P) := rfl

/-- The existing finite-support source theorem constructs the exact data. -/
noncomputable def coordinateInfinityData (M : Model N) (hDVR : PlacesDiscrete M) :
    InfinityDivisorData M hDVR where
  H := coordinateInfinityDivisor M hDVR
  coefficient := coordinateInfinityDivisor_apply M hDVR

end AbcAdaptation.Tripod.Fermat.Proper
