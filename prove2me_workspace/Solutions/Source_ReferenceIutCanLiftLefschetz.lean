/-
Source: Pi1/Orbicurve/LefschetzMain.lean (canLift27_of_complex) at revision
ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftLefschetzAssembly
import Solutions.Source_ReferenceIutCanLiftEmbeddingDescent
import Solutions.Source_ReferenceIutCanLiftCountableRigidity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

/-- The complex core property implies CanLift27 over every field of characteristic zero. -/
theorem canLift27_of_complex (hcomplex : CanLift27Complex) : CanLift27.{0} :=
  canLift27_of_complex_of_descent hcomplex
    (fun f E => normalizationIsCore_of_map f E)
    (fun E => normalizationIsCore_of_countable_models E)

end AbcAdaptation.Reference.Iut.Anabelian
