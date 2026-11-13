/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of Belyi/CurveField/Degree.lean and
Belyi/CurveField/Divisor.lean at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatFunctionFiberDegrees

set_option autoImplicit false

open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The zero and pole fibers of a nonconstant rational function have
its actual finite function-field extension degree. The proof uses actual
integral-closure prime factorization and actual residue-field degrees.
Degrees are over ℚ; the full constant field can be larger than ℚ. -/
theorem functionZeroPoleDegrees {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (hf : Transcendental ℚ f) :
    divisorDegree M (functionZeroDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) ∧
    divisorDegree M (functionPoleDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) :=
  ⟨functionZeroDivisor_degree M hDVR hf, functionPoleDivisor_degree M hDVR hf⟩

end AbcAdaptation.Tripod.Fermat.Proper
