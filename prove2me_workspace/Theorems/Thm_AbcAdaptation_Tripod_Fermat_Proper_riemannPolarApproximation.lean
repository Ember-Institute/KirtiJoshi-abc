/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatFunctionDivisors

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: a divisor becomes bounded by a multiple of the actual polar
divisor of u after adding the divisor of an actual nonzero rational function.
Source: Belyi/CurveField/Riemann.lean:94-158 exists_add_div_le.
At a regular place, the source uses the minimal polynomial over ℚ of the
actual residue of u; at a pole, the polar divisor already contains the place.
The source then uses induction on the finite coefficients of A. -/
theorem riemannPolarApproximation {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (A : Divisor M) :
    ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ,
      A + functionDivisor M hDVR z ≤ l • functionPoleDivisor M hDVR M.u := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
