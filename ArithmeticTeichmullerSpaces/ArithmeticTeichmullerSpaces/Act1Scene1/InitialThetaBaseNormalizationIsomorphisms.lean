import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedBaseNormalizationRing
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseOrbicurvePresentation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's affine Spec functor and compatible integral-closure equivalences.
fidelity: identifies the same seed's ordinary signed base scheme with the
polynomial affine line, and its unsigned base with the polynomial integral
closure in the original elliptic function field. Their original base map
commutes with these isomorphisms.
boundary: Scene1/Derived. The Weierstrass coordinate-ring identification,
orbicurve comparison, cartesianness, core and full producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve Polynomial
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] basePresentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

def baseUnsignedNormalizationRingEquiv :
    integralClosure (↥S.prime.torsionField)[X] S.prime.EK.toAffine.FunctionField ≃ₐ[↥S.prime.torsionField]
      S.baseNormalizationRing false :=
  Genuine.polynomialNormalizationRingAlgEquiv S.prime.EK

def baseSignedNormalizationRingEquiv :
    (↥S.prime.torsionField)[X] ≃ₐ[↥S.prime.torsionField] S.baseNormalizationRing true :=
  Genuine.signedBasePolynomialAlgEquiv S.prime.EK

def baseUnsignedNormalizationIso : S.baseNormalizationScheme false ≅
    Spec (CommRingCat.of
      (integralClosure (↥S.prime.torsionField)[X] S.prime.EK.toAffine.FunctionField)) :=
  Scheme.Spec.mapIso S.baseUnsignedNormalizationRingEquiv.toRingEquiv.toCommRingCatIso.op

def baseSignedNormalizationIso : S.baseNormalizationScheme true ≅
    Spec (CommRingCat.of (↥S.prime.torsionField)[X]) :=
  Scheme.Spec.mapIso S.baseSignedNormalizationRingEquiv.toRingEquiv.toCommRingCatIso.op

/-- The inclusion in the original polynomial normalization model. -/
def polynomialBaseNormalizationMap :
    Spec (CommRingCat.of
      (integralClosure (↥S.prime.torsionField)[X] S.prime.EK.toAffine.FunctionField)) ⟶
        Spec (CommRingCat.of (↥S.prime.torsionField)[X]) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (↥S.prime.torsionField)[X]
      (integralClosure (↥S.prime.torsionField)[X] S.prime.EK.toAffine.FunctionField)))

/-- The ring equivalences preserve the original seed's signed base map. -/
theorem baseNormalizationRingEquiv_square (p : (↥S.prime.torsionField)[X]) :
    S.baseUnsignedNormalizationRingEquiv
        (algebraMap (↥S.prime.torsionField)[X]
          (integralClosure (↥S.prime.torsionField)[X] S.prime.EK.toAffine.FunctionField) p) =
      S.signedBaseNormalizationRingMap (S.baseSignedNormalizationRingEquiv p) :=
  Genuine.baseNormalizationRingEquiv_square S.prime.EK p

theorem baseNormalizationIso_square :
    S.baseUnsignedNormalizationIso.hom ≫ S.polynomialBaseNormalizationMap =
      S.signedBaseNormalizationMap ≫ S.baseSignedNormalizationIso.hom := by
  let P := (↥S.prime.torsionField)[X]
  let C := integralClosure P S.prime.EK.toAffine.FunctionField
  have hr : S.baseUnsignedNormalizationRingEquiv.toRingHom.comp (algebraMap P C) =
      S.signedBaseNormalizationRingMap.toRingHom.comp S.baseSignedNormalizationRingEquiv.toRingHom :=
    RingHom.ext S.baseNormalizationRingEquiv_square
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap P C))
    (CommRingCat.ofHom S.baseUnsignedNormalizationRingEquiv.toRingHom)).symm.trans
      ((congrArg (fun f : P →+* S.baseNormalizationRing false =>
          Spec.map (CommRingCat.ofHom f)) hr).trans
        (Spec.map_comp (CommRingCat.ofHom S.baseSignedNormalizationRingEquiv.toRingHom)
          (CommRingCat.ofHom S.signedBaseNormalizationRingMap.toRingHom)))

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
