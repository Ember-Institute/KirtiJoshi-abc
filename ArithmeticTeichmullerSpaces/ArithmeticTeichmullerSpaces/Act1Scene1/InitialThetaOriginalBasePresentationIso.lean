import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationIso
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaOriginalBasePresentation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the proved original-coordinate ring equivalences and presentation cover category.
fidelity: the original curve and x-line presentations are isomorphic to the
existing normalization presentations as objects of the cover category.
Their coarse isomorphisms are the original scheme comparisons. The original
x-cover square commutes as presentation covers.
boundary: Scene1/Derived. Cartesian and root-stack comparisons, a realization
in arbitrary AG/TG, core and the full geometry producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] basePresentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

def curvePresentationIso : S.baseOrbicurvePresentation false ≅ S.curveOrbicurvePresentation :=
  AffineOrbicurvePresentation.Equiv.toIso
    (X := S.curveOrbicurvePresentation) (Y := S.baseOrbicurvePresentation false)
    S.curveOrbicurvePresentationEquiv

def linePresentationIso : S.baseOrbicurvePresentation true ≅ S.lineOrbicurvePresentation :=
  AffineOrbicurvePresentation.Equiv.toIso
    (X := S.lineOrbicurvePresentation) (Y := S.baseOrbicurvePresentation true)
    S.lineOrbicurvePresentationEquiv

theorem curvePresentationIso_coarse :
    (AffineOrbicurvePresentation.coarseFunctor (k := ↥S.prime.torsionField)).mapIso
      S.curvePresentationIso = S.curveNormalizationIso :=
  (S.curveOrbicurvePresentationEquiv.toIso_coarse).trans
    S.curveOrbicurvePresentationEquiv_coarseIso

theorem linePresentationIso_coarse :
    (AffineOrbicurvePresentation.coarseFunctor (k := ↥S.prime.torsionField)).mapIso
      S.linePresentationIso = S.baseSignedNormalizationIso :=
  (S.lineOrbicurvePresentationEquiv.toIso_coarse).trans
    S.lineOrbicurvePresentationEquiv_coarseIso

theorem originalBasePresentation_coverSquare :
    AffineOrbicurvePresentation.Cover.comp S.curvePresentationIso.hom
        S.curveToLineOrbicurvePresentation =
      AffineOrbicurvePresentation.Cover.comp S.signedBaseOrbicurvePresentation
        S.linePresentationIso.hom := by
  apply AffineOrbicurvePresentation.Cover.ext_f
  exact AlgHom.ext S.curveNormalizationRingMap_algebraMap_poly

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
