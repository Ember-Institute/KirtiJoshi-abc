/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors; The genl contributors

Exact existing parent reduced to three source-backed child statements.
-/
import Solutions.Source_FermatBelyiDifferentConductorAdapters
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity

set_option autoImplicit false
namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Exact replacement body for the existing theorem, with the remaining conductor child explicit. -/
theorem belyiDifferentConductorComparison : BelyiDifferentConductorComparison := by
  exact belyiDifferentConductorComparison_of_exact_children
    belyiActualFieldConductorExtension belyiActualFieldDifferentTower
    tripodGeneratorConductorIdentity

end AbcAdaptation.Tripod.Fermat.Proper
