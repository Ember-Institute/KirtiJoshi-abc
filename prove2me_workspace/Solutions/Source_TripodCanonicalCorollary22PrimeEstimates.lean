import Solutions.Source_TripodCanonicalCorollary22
import Solutions.Source_ReferenceIutChebyshevExplicit
import Solutions.Source_ReferenceIutPrimeCountingExplicit

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- The canonical high-height estimate with the proved cyclic subgroup and prime estimates. -/
theorem canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates
    (P : CurveProviders)
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG)
    (h312 : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData D LT TL QI)) :
    CanonicalCorollary22HighHeightEstimate :=
  canonicalCorollary22HighHeightEstimate_of_cyclicBound P hcore anab
    chebyshevBoundExplicit primeCountingBoundExplicit h312

end AbcAdaptation.Tripod
