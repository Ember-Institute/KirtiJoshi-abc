import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineCoordinateNormalizationMap
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseNormalizationIsomorphisms
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's affine Spec functor, finite maps and Weierstrass fraction field.
fidelity: the same seed's original Weierstrass coordinate ring embeds finitely
in its actual unsigned base normalization. The associated scheme map is finite,
commutes with the original polynomial x-map, and preserves the common function field.
boundary: Scene1/Derived. This constructs the natural comparison map.
Surjectivity and the resulting coordinate-scheme isomorphism remain open;
the orbicurve comparison and full geometric producer remain open.
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

def curveNormalizationRingMap :
    S.prime.EK.toAffine.CoordinateRing →ₐ[↥S.prime.torsionField] S.baseNormalizationRing false :=
  Genuine.coordinateToBaseNormalization S.prime.EK

theorem curveNormalizationRingMap_injective : Function.Injective S.curveNormalizationRingMap :=
  Genuine.coordinateToBaseNormalization_injective S.prime.EK

theorem curveNormalizationRingMap_finite : S.curveNormalizationRingMap.toRingHom.Finite :=
  Genuine.coordinateToBaseNormalization_finite S.prime.EK

@[simp] theorem coe_curveNormalizationRingMap (a : S.prime.EK.toAffine.CoordinateRing) :
    (((S.curveNormalizationRingMap a : S.baseNormalizationRing false) :
      Genuine.normalizationField S.prime.EK 1 ⊥ false) : S.functionFieldClosure) =
        Genuine.ιF S.prime.EK (algebraMap S.prime.EK.toAffine.CoordinateRing
          S.prime.EK.toAffine.FunctionField a) := rfl

theorem curveNormalizationRingMap_algebraMap_poly (p : (↥S.prime.torsionField)[X]) :
    S.curveNormalizationRingMap
        (algebraMap (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing p) =
      S.signedBaseNormalizationRingMap (S.baseSignedNormalizationRingEquiv p) :=
  Genuine.coordinateToBaseNormalization_algebraMap_poly S.prime.EK p

/-- The actual affine scheme of the seed's original Weierstrass coordinate ring. -/
def curveCoordinateScheme : Scheme := Spec (CommRingCat.of S.prime.EK.toAffine.CoordinateRing)

def curveCoordinateToLine : S.curveCoordinateScheme ⟶
    Spec (CommRingCat.of (↥S.prime.torsionField)[X]) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing))

def curveNormalizationMap : S.baseNormalizationScheme false ⟶ S.curveCoordinateScheme :=
  Spec.map (CommRingCat.ofHom S.curveNormalizationRingMap.toRingHom)

instance finite_curveNormalizationMap : AlgebraicGeometry.IsFinite S.curveNormalizationMap :=
  (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr S.curveNormalizationRingMap_finite

/-- The comparison morphism preserves the original x-coordinate projection. -/
theorem curveNormalizationMap_triangle :
    S.curveNormalizationMap ≫ S.curveCoordinateToLine =
      S.signedBaseNormalizationMap ≫ S.baseSignedNormalizationIso.hom := by
  have hr : S.curveNormalizationRingMap.toRingHom.comp
      (algebraMap (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing) =
        S.signedBaseNormalizationRingMap.toRingHom.comp S.baseSignedNormalizationRingEquiv.toRingHom :=
    RingHom.ext S.curveNormalizationRingMap_algebraMap_poly
  exact (Spec.map_comp (CommRingCat.ofHom
      (algebraMap (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing))
      (CommRingCat.ofHom S.curveNormalizationRingMap.toRingHom)).symm.trans
    ((congrArg (fun f : (↥S.prime.torsionField)[X] →+* S.baseNormalizationRing false =>
        Spec.map (CommRingCat.ofHom f)) hr).trans
      (Spec.map_comp (CommRingCat.ofHom S.baseSignedNormalizationRingEquiv.toRingHom)
        (CommRingCat.ofHom S.signedBaseNormalizationRingMap.toRingHom)))

theorem baseNormalizationField_fraction
    (z : Genuine.normalizationField S.prime.EK 1 ⊥ false) :
    ∃ a b : S.prime.EK.toAffine.CoordinateRing, b ≠ 0 ∧
      (S.curveNormalizationRingMap a : Genuine.normalizationField S.prime.EK 1 ⊥ false) /
        (S.curveNormalizationRingMap b : Genuine.normalizationField S.prime.EK 1 ⊥ false) = z :=
  Genuine.coordinateNormalizationField_fraction S.prime.EK z

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
