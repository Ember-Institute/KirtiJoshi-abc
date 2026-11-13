import Definitions.Def_FermatProperCarrier
import Definitions.Def_FermatCurveDerivationEtale
import Definitions.Def_FermatCurveDerivationPolynomial
import Definitions.Def_FermatCurveDerivationBasic
import Definitions.Def_FermatCurveFieldZerosPoles

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: source local obstruction. At a regular ramified place, the
actual derivative with respect to ψ fails to preserve the actual local ring.
Both local rings and ramification indices are those of the existing model;
no derivation or derivation law is supplied as a hypothesis. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (hψP : ψ ∈ P.1) (hram : 1 < ramIdx M hDVR ψ P) :
    ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1 := by
  sorry

/-- OPEN: source generic finite-generation/localization statement. The
actual derivative with respect to ψ preserves all but finitely many actual
local rings containing ψ. The set ranges over every valuative place of M.K. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalDerivativeBadPlacesFinite {N : ℕ} (M : Model N)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | ψ ∈ P.1 ∧
      ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1}.Finite := by
  sorry


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

#print axioms solution
