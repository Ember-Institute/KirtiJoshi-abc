/-
This specializes the P7 and Corollary 2.2 composition in Iut/Tripod/Main.lean
at 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 to the genuine tempered theory.
-/
import Solutions.Source_ReferenceIutChebyshevExplicit
import Solutions.Source_ReferenceIutPrimeCountingExplicit
import Solutions.Source_TripodCanonicalCorollary22
import Solutions.Source_TripodP7FromGenuineTempered

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut AbcAdaptation.Reference.Iut.Anabelian

/-- Corollary 2.2 from the Corollary 3.12 variant on the P7 family of the genuine tempered theory. -/
theorem canonicalCorollary22HighHeightEstimate_of_canLift27_genuineTempered
    (P : CurveProviders)
    (h312 :
      let Pi1 := genuineEtalePi1Theory canLift27
      let T := genuineTemperedPi1Theory canLift27
      ∀ (K : CompactlyBounded) (d : ℕ)
        (X : Corollary312VariantData.{0, 0} (modelAG Pi1) (modelTG Pi1 T)),
        let CF : CurveFactsProp P K d
          (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K d⟩
        let hcore := coreFiniteness_of_modelAG Pi1 P K d
        let CI := curveInputs_from_source P K d CF hcore northcottHyp
          (legendreHeight P K) (twoAdicBound P K)
        IsSourceP7Variant CI (anabelianExistence Pi1 T) X → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate := by
  let Pi1 := genuineEtalePi1Theory canLift27
  let T := genuineTemperedPi1Theory canLift27
  let curveFacts (K : CompactlyBounded) (d : ℕ) : CurveFactsProp P K d
      (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K d⟩
  let coreFiniteness (K : CompactlyBounded) (d : ℕ) := coreFiniteness_of_modelAG Pi1 P K d
  exact canonicalCorollary22HighHeightEstimate_of_thetaDataExistence
    (AG := modelAG Pi1) (TG := modelTG Pi1 T) P
    (TK := fun K => cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c)))
    curveFacts coreFiniteness chebyshevBoundExplicit primeCountingBoundExplicit
    (fun K d => IsSourceP7Variant
      (curveInputs_from_source P K d (curveFacts K d) (coreFiniteness K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)) (anabelianExistence Pi1 T))
    (fun K d =>
      pointThetaDataExistence_from_canLift27_genuineTempered P K d (curveFacts K d) northcottHyp)
    h312

end AbcAdaptation.Tripod
