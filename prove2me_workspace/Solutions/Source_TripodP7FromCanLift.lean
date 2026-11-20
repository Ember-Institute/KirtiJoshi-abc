/-
The source P7 construction in Iut/Tripod/Main.lean at iut revision
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 uses core finiteness for the curve provider.
-/
import Solutions.Source_ReferenceIutCanLiftProp27
import Solutions.Source_ReferenceIutGenuineCore
import Solutions.Source_TripodCoreModel
import Solutions.Source_TripodP7

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut AbcAdaptation.Reference.Iut.Anabelian

/-- The source (P7) witness on the model geometry whose core finiteness follows from CanLift. -/
theorem pointThetaDataExistence_from_canLift27
    {TG : TemperedGeometry (modelAG (genuineEtalePi1Theory canLift27))}
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hN : NorthcottHyp)
    (anab : AnabelianExistence (modelAG (genuineEtalePi1Theory canLift27)) TG) :
    let hcore := coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d
    let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
    ThetaDataExistence (IsSourceP7Variant CI anab) CI.toCorollary22Inputs :=
  pointThetaDataExistence_from_source P K d CF
    (coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d) hN anab

end AbcAdaptation.Tripod
