import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineCoordinateNormalizationSurjective
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaCoordinateNormalizationMap

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the squarefree Weierstrass basis discriminant and affine Spec functor.
fidelity: the same seed's natural coordinate-normalization map is an
isomorphism. It identifies the unsigned base with the original Weierstrass
coordinate scheme and preserves the original x-coordinate projection.
boundary: Scene1/Derived. This resolves the ordinary coordinate-scheme
comparison; arbitrary AG.Orbicurve, cartesianness, core and producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] basePresentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem curveNormalizationRingMap_surjective : Function.Surjective S.curveNormalizationRingMap :=
  Genuine.coordinateToBaseNormalization_surjective S.prime.EK

def curveNormalizationRingEquiv :
    S.prime.EK.toAffine.CoordinateRing ≃ₐ[↥S.prime.torsionField] S.baseNormalizationRing false :=
  Genuine.coordinateBaseNormalizationAlgEquiv S.prime.EK

def curveNormalizationIso : S.baseNormalizationScheme false ≅ S.curveCoordinateScheme :=
  Scheme.Spec.mapIso S.curveNormalizationRingEquiv.toRingEquiv.toCommRingCatIso.op

theorem curveNormalizationIso_hom : S.curveNormalizationIso.hom = S.curveNormalizationMap := rfl

instance isIso_curveNormalizationMap : IsIso S.curveNormalizationMap :=
  S.curveNormalizationIso.isIso_hom

theorem curveNormalizationIso_triangle :
    S.curveNormalizationIso.hom ≫ S.curveCoordinateToLine =
      S.signedBaseNormalizationMap ≫ S.baseSignedNormalizationIso.hom :=
  S.curveNormalizationMap_triangle

theorem curveCoordinateRing_isIntegrallyClosed : IsIntegrallyClosed S.prime.EK.toAffine.CoordinateRing :=
  Genuine.coordinateRing_isIntegrallyClosed S.prime.EK

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
