import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaOrbicurvePresentationCartesian
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnbranchedNormalizationIso

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-!
source-id: JT-SCENE1-ACTUAL-PRESENTATION-CARTESIAN-SOURCE-20261108
source: IUT I Definition 3.1(d),(e); Joshi III `ss:theta-data-fixing2`;
the actual affine presentation category and its proved normalization square.
fidelity: packages only the project-owned affine presentation facts already
proved for this seed: the four covers, the presentation pullback, the coarse
square, and the finite/etale facts for the unsigned map.
boundary: this is not an `AG.Orbicurve` realization. It contains no root-stack
comparison, `AG.IsCartesianSquare`, core, cusp, theta-root, or producer witness.
-/

set_option maxHeartbeats 1000000 in
structure ActualPresentationCartesianSource
    {k : Type u} [Field k]
    (XKu XK CKu CK : AffineOrbicurvePresentation k) where
  signedCover :
    AffineOrbicurvePresentation.Cover XKu CKu
  unsignedCover :
    AffineOrbicurvePresentation.Cover XKu XK
  signedBase :
    AffineOrbicurvePresentation.Cover XK CK
  baseCover :
    AffineOrbicurvePresentation.Cover CKu CK
  presentationPullback :
    IsPullback (C := AffineOrbicurvePresentation k)
      (P := XKu) (X := CKu) (Y := XK) (Z := CK)
      signedCover unsignedCover baseCover signedBase
  coarseSquare :
    unsignedCover.coarseMap ≫ signedBase.coarseMap =
      signedCover.coarseMap ≫ baseCover.coarseMap
  unsignedFinite : IsFinite unsignedCover.coarseMap
  unsignedEtale : Etale unsignedCover.coarseMap

noncomputable def actualPresentationCartesianSource :
    ActualPresentationCartesianSource
      (S.coverOrbicurvePresentation false) (S.baseOrbicurvePresentation false)
      (S.coverOrbicurvePresentation true) (S.baseOrbicurvePresentation true) where
  signedCover := S.signedCoverOrbicurvePresentation
  unsignedCover := S.normalizationOrbicurvePresentationCover false
  signedBase := S.signedBaseOrbicurvePresentation
  baseCover := S.normalizationOrbicurvePresentationCover true
  presentationPullback := S.normalizationOrbicurvePresentation_isPullback
  coarseSquare := S.normalizationOrbicurvePresentation_square
  unsignedFinite := S.normalizationOrbicurvePresentationCover_coarseMap_finite false
  unsignedEtale := S.normalizationOrbicurvePresentationCover_unsigned_coarseMap_etale

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
