import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseNormalizationBranch

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the original coordinate-normalization equivalences and proved branch formula.
fidelity: constructs the original Weierstrass curve and x-line presentations.
The line has multiplicity two exactly on the original two-torsion polynomial.
The original x-map is a presentation cover. Both presentations are equivalent
to the existing normalization presentations and preserve the same coarse square.
boundary: Scene1/Derived. This identifies the ordinary affine presentations;
root-stack realization, arbitrary AG.Orbicurve objects and core remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve Polynomial
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] basePresentationCoefficientAlgebra curveCoordinateRing_isDedekindDomain
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

def curveOrbicurvePresentation : AffineOrbicurvePresentation ↥S.prime.torsionField :=
  AffineOrbicurvePresentation.ofAlgEquiv (S.baseOrbicurvePresentation false)
    S.prime.EK.toAffine.CoordinateRing S.curveNormalizationRingEquiv

def lineOrbicurvePresentation : AffineOrbicurvePresentation ↥S.prime.torsionField :=
  AffineOrbicurvePresentation.ofAlgEquiv (S.baseOrbicurvePresentation true)
    (↥S.prime.torsionField)[X] S.baseSignedNormalizationRingEquiv

def curveOrbicurvePresentationEquiv :
    AffineOrbicurvePresentation.Equiv S.curveOrbicurvePresentation (S.baseOrbicurvePresentation false) :=
  AffineOrbicurvePresentation.ofAlgEquivEquiv (S.baseOrbicurvePresentation false)
    S.prime.EK.toAffine.CoordinateRing S.curveNormalizationRingEquiv

def lineOrbicurvePresentationEquiv :
    AffineOrbicurvePresentation.Equiv S.lineOrbicurvePresentation (S.baseOrbicurvePresentation true) :=
  AffineOrbicurvePresentation.ofAlgEquivEquiv (S.baseOrbicurvePresentation true)
    (↥S.prime.torsionField)[X] S.baseSignedNormalizationRingEquiv

theorem curveOrbicurvePresentation_mult (p : Ideal S.prime.EK.toAffine.CoordinateRing) :
    S.curveOrbicurvePresentation.mult p = 1 := rfl

theorem lineOrbicurvePresentation_mult (p : Ideal (↥S.prime.torsionField)[X]) (hp : p.IsMaximal) :
    S.lineOrbicurvePresentation.mult p =
      if S.prime.EK.twoTorsionPolynomial.toPoly ∈ p then 2 else 1 := by
  have hm := S.baseNormalizationMultiplicity_eq_branch (p.map S.baseSignedNormalizationRingEquiv)
    ((Ideal.isMaximal_map_iff_of_bijective _ S.baseSignedNormalizationRingEquiv.bijective).mpr hp)
  have hmem : S.baseNormalizationBranchPolynomial ∈ p.map S.baseSignedNormalizationRingEquiv ↔
      S.prime.EK.twoTorsionPolynomial.toPoly ∈ p := by
    change S.baseSignedNormalizationRingEquiv S.prime.EK.twoTorsionPolynomial.toPoly ∈
      p.map S.baseSignedNormalizationRingEquiv ↔ _
    exact Ideal.apply_mem_of_equiv_iff
  exact hm.trans (congrArg (fun b : Prop => if b then (2 : ℕ) else 1) (propext hmem))

theorem curveToLinePresentation_ramification
    (q : Ideal S.prime.EK.toAffine.CoordinateRing) (hq : q.IsMaximal) :
    q.ramificationIdx (↥S.prime.torsionField)[X] * S.curveOrbicurvePresentation.mult q =
      S.lineOrbicurvePresentation.mult (q.under (↥S.prime.torsionField)[X]) := by
  have : q.IsMaximal := hq
  have : Algebra.IsIntegral (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing :=
    Genuine.coordinateRing_isIntegral S.prime.EK
  have hp : (q.under (↥S.prime.torsionField)[X]).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  exact (mul_one _).trans ((S.curveCoordinate_ramificationIdx_eq q).trans
    (S.lineOrbicurvePresentation_mult _ hp).symm)

def curveToLineOrbicurvePresentation :
    AffineOrbicurvePresentation.Cover S.curveOrbicurvePresentation S.lineOrbicurvePresentation where
  f := IsScalarTower.toAlgHom ↥S.prime.torsionField (↥S.prime.torsionField)[X]
    S.prime.EK.toAffine.CoordinateRing
  injective := FaithfulSMul.algebraMap_injective (↥S.prime.torsionField)[X]
    S.prime.EK.toAffine.CoordinateRing
  isIntegral := (Genuine.coordinateRing_isIntegral S.prime.EK).isIntegral
  ramification := S.curveToLinePresentation_ramification

theorem curveToLineOrbicurvePresentation_coarseMap :
    S.curveToLineOrbicurvePresentation.coarseMap = S.curveCoordinateToLine := rfl

theorem curveOrbicurvePresentationEquiv_coarseIso :
    S.curveOrbicurvePresentationEquiv.coarseIso = S.curveNormalizationIso := rfl

theorem lineOrbicurvePresentationEquiv_coarseIso :
    S.lineOrbicurvePresentationEquiv.coarseIso = S.baseSignedNormalizationIso := rfl

theorem originalBasePresentation_square :
    S.curveOrbicurvePresentationEquiv.coarseIso.hom ≫ S.curveToLineOrbicurvePresentation.coarseMap =
      S.signedBaseOrbicurvePresentation.coarseMap ≫ S.lineOrbicurvePresentationEquiv.coarseIso.hom :=
  S.curveNormalizationIso_triangle

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
