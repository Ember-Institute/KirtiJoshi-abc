/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatFunctionDivisors

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the actual functions u^k*b_i, 0≤k≤l, for the actual ℚ(u)-basis b_i,
lie in L(l*(u)_infinity + sum_i (b_i)_infinity) and are ℚ-linearly independent.
This statement records their resulting dimension bound, with exactly N
basis entries by Model.degree_u. No free basis, correction divisor, or
dimension function occurs in the type.
Source: Belyi/CurveField/Riemann.lean:169-223, inside the proof of
exists_deg_sub_ell_nsmul_le. -/
theorem riemannBasisPowerLowerBound {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M)
    (hFinite : ∀ A : Divisor M, FiniteDimensional ℚ (riemannRochSpace M hDVR A))
    (l : ℕ) :
    (l + 1) * N ≤ riemannEll M hDVR
      (l • functionPoleDivisor M hDVR M.u + basisPoleCorrection M hDVR) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
