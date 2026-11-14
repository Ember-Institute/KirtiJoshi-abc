/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

DRAFT: exact open source obligation from Belyi/CurveField/Canonical.lean:159,
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Change from the supplied canonical divisor of du to the differential
of an arbitrary transcendental function. The source witness is the actual
q = CurveDeriv.derivAlong φ M.u = du/dφ, nonzero by reciprocal derivatives.
Every proper place, including poles of u and φ, occurs in this identity. -/
theorem canonicalDifferentialChange {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : Transcendental ℚ φ) (K : CanonicalDivisorData M hDVR) :
    ∃ q : M.K, q ≠ 0 ∧ ∀ P : Place M.K,
      K.D P =
        (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + ord M hDVR P q := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
