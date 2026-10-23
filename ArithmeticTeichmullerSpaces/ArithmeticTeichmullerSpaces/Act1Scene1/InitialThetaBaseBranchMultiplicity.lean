import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassBranchMultiplicity
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseBranchLocus

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the proved degree-two ramification law for the original Weierstrass ring.
fidelity: the same arithmetic seed's original x-cover has index two exactly
over its two-torsion branch polynomial, with residue degree one there.
boundary: Scene1/Derived. This does not construct arbitrary AG.Orbicurve
objects, orbicurve cartesianness, core or the full geometric producer.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve Polynomial JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem curveCoordinate_ramificationIdx_two_iff
    (q : Ideal S.prime.EK.toAffine.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx (↥S.prime.torsionField)[X] = 2 ↔
      S.prime.EK.twoTorsionPolynomial.toPoly ∈ q.under (↥S.prime.torsionField)[X] :=
  WeierstrassBranchLocus.ramificationIdx_two_iff_twoTorsion_mem S.prime.EK.toAffine q

theorem curveCoordinate_ramificationIdx_eq
    (q : Ideal S.prime.EK.toAffine.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx (↥S.prime.torsionField)[X] =
      if S.prime.EK.twoTorsionPolynomial.toPoly ∈ q.under (↥S.prime.torsionField)[X]
      then 2 else 1 :=
  WeierstrassBranchLocus.ramificationIdx_eq S.prime.EK.toAffine q

theorem curveCoordinate_inertiaDeg_one_of_branch
    (q : Ideal S.prime.EK.toAffine.CoordinateRing) [q.IsPrime]
    (hq : S.curveBranchElement ∈ q) :
    q.inertiaDeg (↥S.prime.torsionField)[X] = 1 :=
  WeierstrassBranchLocus.inertiaDeg_one_of_branchElement_mem S.prime.EK.toAffine q hq

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
