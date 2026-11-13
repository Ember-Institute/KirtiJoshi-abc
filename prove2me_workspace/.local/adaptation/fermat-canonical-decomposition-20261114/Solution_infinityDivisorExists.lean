import Definitions.Def_FermatInfinityDivisorFiniteSupport

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- The exact coordinate hyperplane coefficient has finite support. -/
theorem solution {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : Nonempty (InfinityDivisorData M hDVR) :=
  ⟨coordinateInfinityData M hDVR⟩
