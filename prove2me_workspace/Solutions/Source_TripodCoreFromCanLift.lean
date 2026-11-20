/-
Sources: lana-agents/iut at 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 (Apache-2.0),
Iut/Anabelian/GenuineEtale.lean and Iut/Tripod/Core.lean, and lana-agents/pi1 at
ca7def953193f861a462aa0831eec8f0a31ff69f (Apache-2.0), Pi1/Orbicurve/LefschetzMain.lean.
-/
import Solutions.Source_ReferenceIutCanLiftLefschetz
import Solutions.Source_ReferenceIutGenuineCore
import Solutions.Source_TripodCoreModel

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut.Anabelian

/-- Complex CanLift supplies the tripod core finiteness for the realized model. -/
theorem coreFiniteness_of_canLift27Complex (hcomplex : CanLift27Complex)
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    CoreFinitenessHyp P K d (modelAG (genuineEtalePi1Theory (canLift27_of_complex hcomplex))) :=
  coreFiniteness_of_modelAG (genuineEtalePi1Theory (canLift27_of_complex hcomplex)) P K d

end AbcAdaptation.Tripod
