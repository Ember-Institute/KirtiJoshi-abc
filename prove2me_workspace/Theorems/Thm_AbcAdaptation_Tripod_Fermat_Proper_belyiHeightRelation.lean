/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors
-/
import Solutions.Source_FermatBelyiHeightComparison
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_polarPresentationHeightSum_of_principalRelation

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem belyiHeightRelation : BelyiHeightRelation :=
  belyiHeightRelation_of_children canonicalCuspPolarLinearEquivalence
    polarPresentationHeightSum_of_principalRelation

end AbcAdaptation.Tripod.Fermat.Proper
