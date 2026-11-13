/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatFunctionDivisors

set_option autoImplicit false

open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the zero and pole fibers of a nonconstant rational function have
degree equal to its actual finite function-field extension degree.
Sources: Belyi/CurveField/Degree.lean:248,308 and Divisor.lean:190-213.
The source counts the actual chart primes over the coordinate prime and
uses the residue-degree/ramification identity in the integral closure. -/
theorem functionZeroPoleDegrees {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (hf : Transcendental ℚ f) :
    divisorDegree M (functionZeroDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) ∧
    divisorDegree M (functionPoleDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
