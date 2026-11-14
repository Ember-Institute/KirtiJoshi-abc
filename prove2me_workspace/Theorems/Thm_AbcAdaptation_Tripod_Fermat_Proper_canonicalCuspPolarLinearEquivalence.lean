/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

DRAFT replacement of the exact existing target. Imported children remain open.
-/
import Solutions.Source_FermatCanonicalCuspComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalDifferentialChange
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiCanonicalCuspCoefficientIdentity

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The actual canonical divisor of du, plus the reduced Belyi cusp divisor,
is linearly equivalent to the polar divisor of φ at every proper place. -/
theorem canonicalCuspPolarLinearEquivalence {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) (K : CanonicalDivisorData M hDVR) :
    ∃ r : M.K, r ≠ 0 ∧ ∀ P : Place M.K,
      K.D P + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P r := by
  exact canonicalCuspPolarLinearEquivalence_of_children canonicalDifferentialChange
    belyiCanonicalCuspCoefficientIdentity M hDVR hRF φ hφ hfin K

end AbcAdaptation.Tripod.Fermat.Proper
