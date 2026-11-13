import Definitions.Def_FermatFunctionFiberDegrees

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- The zero and pole fibers of a nonconstant rational function have
its actual finite function-field extension degree. The proof uses actual
integral-closure prime factorization and actual residue-field degrees.
Degrees are over ℚ; the full constant field can be larger than ℚ. -/
theorem solution {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (hf : Transcendental ℚ f) :
    divisorDegree M (functionZeroDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) ∧
    divisorDegree M (functionPoleDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) :=
  ⟨functionZeroDivisor_degree M hDVR hf, functionPoleDivisor_degree M hDVR hf⟩
