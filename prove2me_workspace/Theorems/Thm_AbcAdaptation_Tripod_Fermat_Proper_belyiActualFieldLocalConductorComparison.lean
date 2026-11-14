/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; see SOURCE_LEDGER.md.
-/
import Definitions.Def_FermatBelyiConductorExtensionChildren

set_option autoImplicit false
namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN exact arithmetic port: Heights/Different/Conductor.lean:104 log_placeNorm_div_le. The lower-only dependency is
Bounds.lean:169 ramificationIdx'_sub_one_le_multiplicity and :252 sum_le_diffContrib;
Mathlib pow_sub_one_dvd_differentIdeal proves e−1 ≤ ord_P(different).
Do not import Heights.Different.Bounds or SerreBound: their upper bounds are not needed.
Actual fields and actual inclusion are fixed by the proposition carrier. -/
theorem belyiActualFieldLocalConductorComparison : BelyiActualFieldLocalConductorComparison := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
