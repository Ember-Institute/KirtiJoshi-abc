import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

open scoped Classical
open AbcAdaptation.Tripod.Fermat.Proper

theorem AbcAdaptation.Tripod.Fermat.Proper.belyiCanonicalCuspCoefficientIdentity {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    ∀ P : Place M.K,
      (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
        else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1)) := by sorry
