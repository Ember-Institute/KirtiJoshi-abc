import Solutions.Source_ReferenceIutCanLiftComplexFromFricke
import Solutions.Source_ReferenceIutCanLiftFinal
import Solutions.Source_ReferenceIutCanLiftLefschetz

namespace AbcAdaptation.Reference.Iut.Anabelian

/-- The complex case of CanLift Proposition 2.7 from Fricke trace integrality. -/
theorem canLift27Complex : CanLift27Complex :=
  canLift27Complex_of_fricke_integrality CanLiftAnalytic.M2.normalFormTraceIntegrality

/-- CanLift Proposition 2.7 over fields of characteristic zero. -/
theorem canLift27 : CanLift27.{0} :=
  canLift27_of_complex canLift27Complex

end AbcAdaptation.Reference.Iut.Anabelian
