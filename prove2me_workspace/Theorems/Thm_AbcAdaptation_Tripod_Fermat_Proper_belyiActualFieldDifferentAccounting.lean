/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; see SOURCE_LEDGER.md.
-/
import Definitions.Def_FermatBelyiConductorExtensionChildren
import Solutions.Source_FermatBelyiDifferentAccounting

set_option autoImplicit false
open NumberField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The pinned source grouped norm identity and finite support, for the actual inclusion.
Both accounting conjuncts and the full point-field normalization are unchanged. -/
theorem belyiActualFieldDifferentAccounting : BelyiActualFieldDifferentAccounting := by
  intro N M hRF φ x hgood
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  exact ⟨ConductorExtensionSource.diffContrib_support_finite x.fieldOf,
    ConductorExtensionSource.log_absNorm_differentIdeal_div_eq_finsum x.fieldOf⟩

end AbcAdaptation.Tripod.Fermat.Proper
