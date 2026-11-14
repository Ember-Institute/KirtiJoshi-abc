/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; validation and source mappings are recorded with this unit.
-/
import Definitions.Def_FermatBelyiDifferentConductorChildren

set_option autoImplicit false
namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN exact port: Heights/Different/Conductor.lean:170 cond_le_cond_add.
The complete pinned proof body and necessary source files are copied under reference/.
Port only the local lower bound e-1 ≤ different exponent; no Serre upper bound is needed.
Do not close this with an axiom, a smaller field, or a height surrogate. -/
theorem belyiActualFieldConductorExtension : BelyiActualFieldConductorExtension := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
