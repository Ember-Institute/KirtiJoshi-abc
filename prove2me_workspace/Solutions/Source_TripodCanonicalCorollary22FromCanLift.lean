/-
Source: lana-agents/iut, 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 (Apache-2.0),
Iut/Tripod/Main.lean (abc_of_variant) and Iut/Tripod/ClassicalAbcGenuineCanLift.lean.
-/
import Solutions.Source_ReferenceIutChebyshevExplicit
import Solutions.Source_ReferenceIutPrimeCountingExplicit
import Solutions.Source_TripodCanonicalCorollary22
import Solutions.Source_TripodP7FromCanLift

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut AbcAdaptation.Reference.Iut.Anabelian

/-- Corollary 2.2 on the source P7 bundles for the model supplied by CanLift. -/
theorem canonicalCorollary22HighHeightEstimate_of_canLift27
    {TG : TemperedGeometry (modelAG (genuineEtalePi1Theory canLift27))}
    (P : CurveProviders)
    (anab : AnabelianExistence (modelAG (genuineEtalePi1Theory canLift27)) TG)
    (h312 : ∀ (K : CompactlyBounded) (d : ℕ)
      (X : Corollary312VariantData.{0, 0} (modelAG (genuineEtalePi1Theory canLift27)) TG),
      let CF : CurveFactsProp P K d
          (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K d⟩
      let hcore := coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d
      let CI := curveInputs_from_source P K d CF hcore northcottHyp
        (legendreHeight P K) (twoAdicBound P K)
      IsSourceP7Variant CI anab X → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate := by
  let curveFacts (K : CompactlyBounded) (d : ℕ) : CurveFactsProp P K d
      (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K d⟩
  let coreFiniteness (K : CompactlyBounded) (d : ℕ) :=
    coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d
  exact canonicalCorollary22HighHeightEstimate_of_thetaDataExistence
    (AG := modelAG (genuineEtalePi1Theory canLift27)) (TG := TG) P
    (TK := fun K => cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c)))
    curveFacts coreFiniteness chebyshevBoundExplicit primeCountingBoundExplicit
    (fun K d => IsSourceP7Variant
      (curveInputs_from_source P K d (curveFacts K d) (coreFiniteness K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)) anab)
    (fun K d => pointThetaDataExistence_from_canLift27 P K d (curveFacts K d) northcottHyp anab)
    h312

end AbcAdaptation.Tripod
