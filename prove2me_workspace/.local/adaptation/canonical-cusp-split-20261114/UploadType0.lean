import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

open scoped Classical
open AbcAdaptation.Tripod.Fermat.Proper

theorem AbcAdaptation.Tripod.Fermat.Proper.canonicalDifferentialChange {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : Transcendental ℚ φ) (K : CanonicalDivisorData M hDVR) :
    ∃ q : M.K, q ≠ 0 ∧ ∀ P : Place M.K,
      K.D P =
        (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + ord M hDVR P q := by sorry
