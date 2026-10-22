import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionFields
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Realize.lean`, integral-closure realization.
fidelity: actual normalization rings and affine spectra for the same seed's
finite fixed fields, with the signed-quotient integral ring map and induced Spec map.
boundary: Scene1/Derived. This does not assert etaleness, cartesian covering,
orbifold multiplicity, core or theta-root identification.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory
open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped IntermediateField.algebraAdjoinAdjoin Classical
universe u
noncomputable section

set_option synthInstance.maxHeartbeats 1000000
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

abbrev coverNormalizationRing (pm : Bool) :=
  Genuine.coverCoordinateRing S.prime.EK S.prime.ℓ S.prime.M pm

/-- The actual affine scheme of the normalization ring, not a model flag. -/
def coverNormalizationScheme (pm : Bool) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (S.coverNormalizationRing pm))

instance affine_coverNormalizationScheme (pm : Bool) :
    AlgebraicGeometry.IsAffine (S.coverNormalizationScheme pm) := by
  unfold coverNormalizationScheme
  infer_instance

theorem coverNormalizationRing_notField (pm : Bool) : ¬ IsField (S.coverNormalizationRing pm) :=
  Genuine.notField_coverCoordinateRing S.prime.EK S.prime.ℓ S.prime.M pm

def signedCoverNormalizationRingMap : S.coverNormalizationRing true →ₐ[↥S.prime.torsionField]
    S.coverNormalizationRing false :=
  Genuine.signedNormalizationRingMap S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverNormalizationRingMap_injective :
    Function.Injective S.signedCoverNormalizationRingMap :=
  Genuine.signedNormalizationRingMap_injective S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverNormalizationRingMap_isIntegral :
    S.signedCoverNormalizationRingMap.toRingHom.IsIntegral :=
  Genuine.signedNormalizationRingMap_isIntegral S.prime.EK S.prime.ℓ S.prime.M

/-- The contravariant affine morphism induced by the proved signed inclusion. -/
def signedCoverNormalizationMap : S.coverNormalizationScheme false ⟶
    S.coverNormalizationScheme true :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom S.signedCoverNormalizationRingMap.toRingHom)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
