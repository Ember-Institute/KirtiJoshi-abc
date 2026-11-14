/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Modified adaptation, 2026-11-14: exact concrete Northcott proof from
refer/iut/Iut/Tripod/Northcott.lean. Uses the existing independent tripod
carrier and Mathlib only. Source hashes and revision status: SOURCE_MANIFEST.json.
-/
import Definitions.Def_TripodNorthcottInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open Polynomial Northcott

open scoped Classical in
/-- Source proof of `Iut.Tripod.finite_roots_polySet` (line 150), directly
using Mathlib's finite-coefficient polynomial-root union theorem. -/
theorem northcottFiniteRoots : Northcott.FiniteRoots := by
  intro d H
  exact bUnion_roots_finite (Int.castRingHom Qbar) d (Set.finite_Icc _ _)

end AbcAdaptation.Tripod
