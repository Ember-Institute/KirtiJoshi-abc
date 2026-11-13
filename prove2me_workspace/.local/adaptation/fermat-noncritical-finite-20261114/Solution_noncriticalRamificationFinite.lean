import Definitions.Def_FermatCurveFieldZerosPoles
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- A nonconstant actual function is ramified at finitely many places.
Source combination: every ramified place is a pole or a regular place
where the actual derivative does not preserve the local ring. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | 1 < ramIdx M hDVR ψ P}.Finite := by
  letI : IsCurveField M.K := M.isCurveField
  refine ((Place.finite_setOf_notMem ψ).union
    (noncriticalDerivativeBadPlacesFinite M ψ hψ)).subset ?_
  intro P hP
  by_cases hψP : ψ ∈ P.1
  · exact Or.inr ⟨hψP, noncriticalRegularRamifiedDerivNotMem M hDVR ψ hψ P hψP hP⟩
  · exact Or.inl hψP
