import Definitions.Def_FermatNoncriticalFunctions

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement with the original signature. Finite support holds
for every actual φ, so the existing hRF and hφ parameters remain compatible. -/
theorem solution {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ) :
    (cusps M hDVR φ).Finite :=
  model_cuspsFinite M hDVR φ
