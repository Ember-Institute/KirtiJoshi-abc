/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/
import Definitions.Def_FermatBelyiConductorExtensionChildren
import Solutions.Source_FermatConductorLocalComparison

set_option autoImplicit false
open NumberField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Source Conductor.lean:104–136 on the unchanged actual image-field inclusion.
The source proof uses only the lower bound e−1 ≤ ord_P(different). -/
theorem belyiActualFieldLocalConductorComparison : BelyiActualFieldLocalConductorComparison := by
  intro N M hRF φ x hgood
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  intro u
  exact ConductorExtensionSource.log_placeNorm_div_le x.fieldOf u

end AbcAdaptation.Tripod.Fermat.Proper
