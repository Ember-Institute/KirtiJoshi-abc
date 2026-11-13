/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: finite generation of the actual complement coordinate ring,
extending the three fixed tripod generators.
Source: pinned Genl/Curves/BelyiDescent.lean:289-304 and its invocation of
exists_finset_adjoin_eq_coordRing. Nonempty cusp support follows from
transcendence of φ; regularity of φ,φ⁻¹,(1-φ)⁻¹ follows off the actual cusps. -/
theorem cuspGeneratorsExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    Nonempty (CuspGenerators M hDVR φ hfin) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
