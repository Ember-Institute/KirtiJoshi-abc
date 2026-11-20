/-
The model uniformizations follow OrbicurveCores/S1/Main.lean, lines 82–108,
at 61616dcd77fbe45c083a8ebfa7cc80728f86e841. This connects them to
the local CanLift assembly from Fricke normal forms.
-/
import Solutions.Source_ReferenceIutCanLiftFrickeTraceTransport
import Solutions.Source_ReferenceIutCanLiftTakeuchiModelUniformizations

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

/-- Fricke normal-form trace integrality suffices for complex CanLift using the certified
uniformizations of the four Takeuchi model curves. -/
theorem canLift27Complex_of_fricke_integrality
    (hNormal : CanLiftAnalytic.M2.NormalFormTraceIntegrality) : CanLift27Complex :=
  canLift27Complex_of_fricke_normal_form hNormal CanLiftAnalytic.Takeuchi.exists_takeuchiPair_ccurve

end AbcAdaptation.Reference.Iut.Anabelian
