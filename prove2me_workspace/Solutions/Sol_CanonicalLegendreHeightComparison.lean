/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of Iut/Tripod/Height.lean and TwoAdic.lean.
Archived source hashes are recorded in this unit's source-consumer.json.
Historical upstream revision is unverified. No Iut or Genl module is imported.
-/
import Definitions.Def_TripodLegendreHeightComparisonComposition
import Theorems.Thm_AbcAdaptation_Tripod_legendreFiniteUpperBound
import Theorems.Thm_AbcAdaptation_Tripod_legendreFiniteLowerBound
import Theorems.Thm_AbcAdaptation_Tripod_legendreArchimedeanTripleBound
import Theorems.Thm_AbcAdaptation_Tripod_legendreZeroJRootOfUnity

set_option autoImplicit false

open AbcAdaptation.Tripod

theorem solution : CanonicalLegendreHeightComparison :=
  canonicalLegendreHeightComparison_of_source_children
    legendreFiniteUpperBound legendreFiniteLowerBound
    legendreArchimedeanTripleBound legendreZeroJRootOfUnity
