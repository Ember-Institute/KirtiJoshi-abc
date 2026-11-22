import Solutions.Source_TripodCanonicalCorollary22FromGenuineTempered
import Solutions.Source_TripodProviders

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut AbcAdaptation.Reference.Iut.Anabelian

/-- Corollary 2.2 for the actual Legendre curve providers and the genuine tempered theory,
conditional on Corollary 3.12 on their P7 family. -/
theorem canonicalCorollary22HighHeightEstimate_of_tripodProviders
    (h312 :
      let Pi1 := genuineEtalePi1Theory canLift27
      let T := genuineTemperedPi1Theory canLift27
      ∀ (K : CompactlyBounded) (d : ℕ)
        (X : Corollary312VariantData.{0, 0} (modelAG Pi1) (modelTG Pi1 T)),
        let CF : CurveFactsProp tripodProviders K d
          (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) :=
          ⟨cyclicBoundOdd tripodProviders K d⟩
        let hcore := coreFiniteness_of_modelAG Pi1 tripodProviders K d
        let CI := curveInputs_from_source tripodProviders K d CF hcore northcottHyp
          (legendreHeight tripodProviders K) (twoAdicBound tripodProviders K)
        IsSourceP7Variant CI (anabelianExistence Pi1 T) X → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate :=
  canonicalCorollary22HighHeightEstimate_of_canLift27_genuineTempered tripodProviders h312

end AbcAdaptation.Tripod
