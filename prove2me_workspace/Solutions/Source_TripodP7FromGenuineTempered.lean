/-
Source: Iut/Tripod/Main.lean at iut revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
The P7 construction uses the anabelian witnesses of the model orbicurves.
-/
import Solutions.Source_ReferenceIutGenuineTempered
import Solutions.Source_TripodP7FromCanLiftTempered

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut AbcAdaptation.Reference.Iut.Anabelian

/-- The source P7 witness with the genuine étale and tempered groups of the CanLift model. -/
theorem pointThetaDataExistence_from_canLift27_genuineTempered
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hN : NorthcottHyp) :
    let Pi1 := genuineEtalePi1Theory canLift27
    let T := genuineTemperedPi1Theory canLift27
    let hcore := coreFiniteness_of_modelAG Pi1 P K d
    let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
    ThetaDataExistence (IsSourceP7Variant CI (anabelianExistence Pi1 T)) CI.toCorollary22Inputs :=
  pointThetaDataExistence_from_canLift27_of_temperedTheory
    (genuineTemperedPi1Theory canLift27) P K d CF hN

end AbcAdaptation.Tripod
