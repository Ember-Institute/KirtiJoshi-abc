import Definitions.Def_FermatRiemannPolarApproximation

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- An actual nonzero function moves A below a multiple of the pole divisor of u. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (A : Divisor M) :
    ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ,
      A + functionDivisor M hDVR z ≤ l • functionPoleDivisor M hDVR M.u := by
  letI : IsCurveField M.K := M.isCurveField
  exact RiemannApproximation.exists_add_div_le M hDVR M.transcendental_u A
