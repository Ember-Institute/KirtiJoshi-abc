import Definitions.Def_FermatCurveDerivationAdjoin
import Mathlib.RingTheory.DiscreteValuationRing.Basic
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] (O : ValuationSubring K)



theorem AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_mem {π : K} (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
    (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
    (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
    [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
    {x : K} (hx : x ∈ O) : derivAlong π x ∈ O := by sorry
