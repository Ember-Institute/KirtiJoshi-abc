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

/-- The explicit prime estimates with Corollary 3.12 on the source (P7) bundles. -/
theorem canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates_on_sourceP7
    (P : CurveProviders)
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG)
    (h312 : ∀ (K : CompactlyBounded) (d : ℕ) (X : Corollary312VariantData.{0, 0} AG TG),
      let CF : CurveFactsProp P K d
          (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K d⟩
      let CI := curveInputs_from_source P K d CF (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)
      IsSourceP7Variant CI anab X → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate :=
  canonicalCorollary22HighHeightEstimate_of_sourceP7 P
    (TK := fun K => cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c)))
    (fun K d => ⟨cyclicBoundOdd P K d⟩) hcore anab
    chebyshevBoundExplicit primeCountingBoundExplicit h312

end AbcAdaptation.Tripod
