/-
The source P7 construction in Iut/Tripod/Main.lean at iut revision
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 uses the model anabelian existence theorem.
-/
import Solutions.Source_ReferenceIutAnabelianExistence
import Solutions.Source_TripodP7FromCanLift

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut AbcAdaptation.Reference.Iut.Anabelian

/-- The source P7 witness on the CanLift model with the supplied tempered fundamental groups. -/
theorem pointThetaDataExistence_from_canLift27_of_temperedTheory
    (T : TemperedPi1Theory (genuineEtalePi1Theory canLift27))
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hN : NorthcottHyp) :
    let hcore := coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d
    let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
    ThetaDataExistence
      (IsSourceP7Variant CI (anabelianExistence (genuineEtalePi1Theory canLift27) T))
      CI.toCorollary22Inputs :=
  pointThetaDataExistence_from_canLift27
    (TG := modelTG (genuineEtalePi1Theory canLift27) T) P K d CF hN
    (anabelianExistence (genuineEtalePi1Theory canLift27) T)

end AbcAdaptation.Tripod
