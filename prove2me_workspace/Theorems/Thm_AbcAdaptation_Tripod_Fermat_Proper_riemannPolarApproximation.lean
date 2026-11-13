/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of Belyi/CurveField/Riemann.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannPolarApproximation

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- An actual nonzero function moves A below a multiple of the pole divisor of u. -/
theorem riemannPolarApproximation {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (A : Divisor M) :
    ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ,
      A + functionDivisor M hDVR z ≤ l • functionPoleDivisor M hDVR M.u := by
  letI : IsCurveField M.K := M.isCurveField
  exact RiemannApproximation.exists_add_div_le M hDVR M.transcendental_u A

end AbcAdaptation.Tripod.Fermat.Proper
