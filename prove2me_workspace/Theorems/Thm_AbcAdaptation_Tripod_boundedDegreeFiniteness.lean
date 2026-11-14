/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Modified adaptation, 2026-11-14: exact concrete Northcott proof from
refer/iut/Iut/Tripod/Northcott.lean. Uses the existing independent tripod
carrier and Mathlib only. Source hashes and revision status: SOURCE_MANIFEST.json.
-/
import Definitions.Def_TripodNorthcottComposition
import Theorems.Thm_AbcAdaptation_Tripod_northcottFiniteRoots
import Theorems.Thm_AbcAdaptation_Tripod_northcottPolynomialWitness

set_option autoImplicit false

theorem AbcAdaptation.Tripod.boundedDegreeFiniteness :
    AbcAdaptation.Tripod.BoundedDegreeFiniteness :=
  AbcAdaptation.Tripod.boundedDegreeFiniteness_of_northcott_children
    AbcAdaptation.Tripod.northcottFiniteRoots
    AbcAdaptation.Tripod.northcottPolynomialWitness
