/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

DECOMPOSITION DRAFT: the mathematical proof below remains open.
Sources: Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8,
CurveField/Canonical.lean:159 and CurveField/BelyiRelation.lean:85.
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The actual canonical divisor of du, plus the reduced Belyi cusp divisor,
is linearly equivalent to the polar divisor of φ. The equality includes every
proper place. The witness is an actual nonzero element of M.K.

Source proof route: q = du/dφ, and r = (φ * (φ - 1)) * q.
CanonicalDivisorData.coefficient identifies the supplied K with div(du).
No plane adjunction, projective height, or height comparison enters this child. -/
theorem canonicalCuspPolarLinearEquivalence {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) (K : CanonicalDivisorData M hDVR) :
    ∃ r : M.K, r ≠ 0 ∧ ∀ P : Place M.K,
      K.D P + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P r := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
