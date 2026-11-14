/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; see SOURCE_LEDGER.md.
-/
import Solutions.Source_FermatBelyiConductorExtensionAdapters
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldLocalConductorComparison
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentAccounting

set_option autoImplicit false
namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Original exact statement, now composed from the two explicit arithmetic children. -/
theorem belyiActualFieldConductorExtension : BelyiActualFieldConductorExtension :=
  belyiActualFieldConductorExtension_of_local_and_accounting
    belyiActualFieldLocalConductorComparison belyiActualFieldDifferentAccounting

end AbcAdaptation.Tripod.Fermat.Proper
