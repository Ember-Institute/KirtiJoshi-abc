import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutGenuineTempered
import Solutions.Source_TripodP7FromGenuineTempered

set_option autoImplicit false

open AbcAdaptation.Reference.Iut.Anabelian
open JoshiTeich.ReferenceIut.Anabelian (Orbicurve)
open scoped Classical

universe u

example {k : Type u} [Field k] [CharZero k] (X : Orbicurve k) :
    modelTemperedPresentation X =
      ⟨modelNormalizationOrbifold X, (modelEtalePi1Equiv X).toMulEquiv.toMonoidHom,
        (modelEtalePi1Equiv X).continuous⟩ := by
  rw [modelTemperedPresentation, dif_pos (inferInstance : CharZero k)]

example {k : Type u} [Field k] (h : ¬ CharZero k) (X : Orbicurve k) :
    modelTemperedPresentation X =
      ⟨TemperedFundamentalGroups.Orbicurve.orbicurveOrbifold X.E X.level X.M X.pm,
        1, continuous_const⟩ := by
  rw [modelTemperedPresentation, dif_neg h]

#check genuineTemperedPi1Theory
#check AbcAdaptation.Tripod.pointThetaDataExistence_from_canLift27_genuineTempered

#print axioms genuinePi1_eq_profiniteInertiaQuotient
#print axioms modelNormalizationOrbifold
#print axioms modelEtalePi1Equiv
#print axioms modelTemperedPresentation
#print axioms genuineTemperedPi1Theory
#print axioms AbcAdaptation.Tripod.pointThetaDataExistence_from_canLift27_genuineTempered
