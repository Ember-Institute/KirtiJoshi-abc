import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalization
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Realize.lean`, normalization diagram;
Mathlib `AlgebraicGeometry.IsFinite.SpecMap_iff`.
fidelity: proves finiteness of the actual signed normalization map, constructs
the level-one normalization rings and the covering-to-base inclusions for the
same seed, and proves finiteness and commutativity of their affine Spec diagram.
boundary: Scene1/Derived. Etaleness, cartesianness, orbifold multiplicity, core
and theta-root identification remain open.
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

theorem signedCoverNormalizationRingMap_finite :
    S.signedCoverNormalizationRingMap.toRingHom.Finite :=
  FunctionFieldNormalization.ringMap_finite (Genuine.transcendental_xG S.prime.EK) _

instance finite_signedCoverNormalizationMap :
    AlgebraicGeometry.IsFinite S.signedCoverNormalizationMap :=
  (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr S.signedCoverNormalizationRingMap_finite

/-- The normalization at level one, in the same seed's signed or unsigned base field. -/
abbrev baseNormalizationRing (pm : Bool) :=
  Genuine.coverCoordinateRing S.prime.EK 1 ⊥ pm

def baseNormalizationScheme (pm : Bool) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (S.baseNormalizationRing pm))

instance affine_baseNormalizationScheme (pm : Bool) :
    AlgebraicGeometry.IsAffine (S.baseNormalizationScheme pm) := by
  unfold baseNormalizationScheme
  infer_instance

theorem normalizationField_contains_base (pm : Bool) :
    Genuine.normalizationField S.prime.EK 1 ⊥ pm ≤
      Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M pm :=
  FunctionFieldNormalization.rebaseField_mono (Genuine.baseField_eq_xLine S.prime.EK)
    (S.functionFieldCoverField_contains_base pm)

/-- The base-to-cover normalization map extends the actual ambient field inclusion. -/
def baseToCoverNormalizationRingMap (pm : Bool) :
    S.baseNormalizationRing pm →ₐ[↥S.prime.torsionField] S.coverNormalizationRing pm :=
  FunctionFieldNormalization.ringMap (S.normalizationField_contains_base pm)

@[simp] theorem coe_baseToCoverNormalizationRingMap (pm : Bool)
    (a : S.baseNormalizationRing pm) :
    ((S.baseToCoverNormalizationRingMap pm a :
      Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M pm) :
        S.functionFieldClosure) =
    ((a : Genuine.normalizationField S.prime.EK 1 ⊥ pm) : S.functionFieldClosure) := rfl

theorem baseToCoverNormalizationRingMap_injective (pm : Bool) :
    Function.Injective (S.baseToCoverNormalizationRingMap pm) :=
  FunctionFieldNormalization.ringMap_injective _

theorem baseToCoverNormalizationRingMap_finite (pm : Bool) :
    (S.baseToCoverNormalizationRingMap pm).toRingHom.Finite :=
  FunctionFieldNormalization.ringMap_finite (Genuine.transcendental_xG S.prime.EK) _

def coverToBaseNormalizationMap (pm : Bool) :
    S.coverNormalizationScheme pm ⟶ S.baseNormalizationScheme pm :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (S.baseToCoverNormalizationRingMap pm).toRingHom)

instance finite_coverToBaseNormalizationMap (pm : Bool) :
    AlgebraicGeometry.IsFinite (S.coverToBaseNormalizationMap pm) :=
  (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr (S.baseToCoverNormalizationRingMap_finite pm)

def signedBaseNormalizationRingMap :
    S.baseNormalizationRing true →ₐ[↥S.prime.torsionField] S.baseNormalizationRing false :=
  Genuine.signedNormalizationRingMap S.prime.EK 1 ⊥

theorem signedBaseNormalizationRingMap_finite :
    S.signedBaseNormalizationRingMap.toRingHom.Finite :=
  FunctionFieldNormalization.ringMap_finite (Genuine.transcendental_xG S.prime.EK) _

def signedBaseNormalizationMap : S.baseNormalizationScheme false ⟶
    S.baseNormalizationScheme true :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom S.signedBaseNormalizationRingMap.toRingHom)

instance finite_signedBaseNormalizationMap :
    AlgebraicGeometry.IsFinite S.signedBaseNormalizationMap :=
  (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr S.signedBaseNormalizationRingMap_finite

/-- Both paths are inclusions of the same ambient values in the same normalization ring. -/
theorem normalizationRingMap_square :
    (S.baseToCoverNormalizationRingMap false).comp S.signedBaseNormalizationRingMap =
      S.signedCoverNormalizationRingMap.comp (S.baseToCoverNormalizationRingMap true) := by
  ext a
  rfl

theorem normalizationMap_square :
    S.coverToBaseNormalizationMap false ≫ S.signedBaseNormalizationMap =
      S.signedCoverNormalizationMap ≫ S.coverToBaseNormalizationMap true := by
  have h := congrArg (fun f : S.baseNormalizationRing true →ₐ[↥S.prime.torsionField]
      S.coverNormalizationRing false =>
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom)) S.normalizationRingMap_square
  exact (AlgebraicGeometry.Spec.map_comp
    (CommRingCat.ofHom S.signedBaseNormalizationRingMap.toRingHom)
    (CommRingCat.ofHom (S.baseToCoverNormalizationRingMap false).toRingHom)).symm.trans
      (h.trans (AlgebraicGeometry.Spec.map_comp
        (CommRingCat.ofHom (S.baseToCoverNormalizationRingMap true).toRingHom)
        (CommRingCat.ofHom S.signedCoverNormalizationRingMap.toRingHom)))

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
