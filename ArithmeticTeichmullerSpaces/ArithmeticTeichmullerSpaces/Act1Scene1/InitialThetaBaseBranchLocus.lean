import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassBranchRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaCoordinateNormalizationIso

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the proved derivative criterion for the same seed's original coordinate ring.
fidelity: computes the etale locus and ramification-one condition of the seed's
actual x-projection. The branch element squares to its original two-torsion
polynomial. The source scheme is identified with its unsigned normalization.
boundary: Scene1/Derived. This does not supply arbitrary AG.Orbicurve objects,
the orbicurve cartesian square, core or the full producer.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve Polynomial JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

def curveBranchElement : S.prime.EK.toAffine.CoordinateRing :=
  WeierstrassBranchLocus.branchElement S.prime.EK.toAffine

theorem curveBranchElement_sq : S.curveBranchElement ^ 2 =
    algebraMap (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing
      S.prime.EK.twoTorsionPolynomial.toPoly :=
  WeierstrassBranchLocus.branchElement_sq S.prime.EK.toAffine

theorem curveCoordinate_isEtaleAt_iff (q : Ideal S.prime.EK.toAffine.CoordinateRing) [q.IsPrime] :
    Algebra.IsEtaleAt (↥S.prime.torsionField)[X] q ↔ S.curveBranchElement ∉ q :=
  WeierstrassBranchLocus.isEtaleAt_iff S.prime.EK.toAffine q

theorem curveCoordinate_etaleLocus :
    Algebra.etaleLocus (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing =
      PrimeSpectrum.basicOpen S.curveBranchElement :=
  WeierstrassBranchLocus.etaleLocus_eq_basicOpen S.prime.EK.toAffine

theorem curveCoordinate_ramificationIdx_one_iff
    (q : Ideal S.prime.EK.toAffine.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx (↥S.prime.torsionField)[X] = 1 ↔
      S.prime.EK.twoTorsionPolynomial.toPoly ∉ q.under (↥S.prime.torsionField)[X] :=
  WeierstrassBranchLocus.ramificationIdx_one_iff_twoTorsion_not_mem S.prime.EK.toAffine q

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
