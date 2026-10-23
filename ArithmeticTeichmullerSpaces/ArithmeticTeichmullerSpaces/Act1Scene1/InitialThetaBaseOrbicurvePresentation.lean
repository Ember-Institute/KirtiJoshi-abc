import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaOrbicurvePresentation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's Galois ramification comparison and normalization multiplicities.
fidelity: constructs the base affine orbicurve presentations from the original
level-one normalization rings. Their signed multiplicities are the actual
ramification indices; their unsigned multiplicities are one.
boundary: Scene1/Derived. These are coordinate-ring presentations, without an
assumed comparison to root stacks or arbitrary AG.Orbicurve objects.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance basePresentationCoefficientAlgebra (pm : Bool) :
    Algebra ↥S.prime.torsionField (S.baseNormalizationRing pm) :=
  normalizationCoefficientAlgebra S.prime.EK 1 ⊥ pm

def baseNormalizationMultiplicity : (pm : Bool) → Ideal (S.baseNormalizationRing pm) → ℕ
  | false => fun _ => 1
  | true => FunctionFieldNormalization.ramificationMultiplicity
      (Genuine.normalizationField_signed_le_unsigned S.prime.EK 1 ⊥)

theorem baseNormalizationMultiplicity_pos (pm : Bool)
    (v : Ideal (S.baseNormalizationRing pm)) (hv : v.IsMaximal) :
    0 < S.baseNormalizationMultiplicity pm v := by
  cases pm
  · exact Nat.one_pos
  · exact FunctionFieldNormalization.ramificationMultiplicity_pos
      (Genuine.transcendental_xG S.prime.EK) _ v hv

theorem baseNormalizationMultiplicity_finite (pm : Bool) :
    {v : Ideal (S.baseNormalizationRing pm) |
      v.IsMaximal ∧ S.baseNormalizationMultiplicity pm v ≠ 1}.Finite := by
  cases pm
  · simp [baseNormalizationMultiplicity]
  · exact FunctionFieldNormalization.finite_ramificationMultiplicity
      (Genuine.transcendental_xG S.prime.EK) _

/-- The base presentations use the existing level-one normalization schemes. -/
def baseOrbicurvePresentation (pm : Bool) : AffineOrbicurvePresentation ↥S.prime.torsionField where
  A := S.baseNormalizationRing pm
  finiteType := Genuine.finiteType_coverCoordinateRing S.prime.EK 1 ⊥ pm
  not_isField := Genuine.notField_coverCoordinateRing S.prime.EK 1 ⊥ pm
  mult := S.baseNormalizationMultiplicity pm
  mult_pos := S.baseNormalizationMultiplicity_pos pm
  finite_mult := S.baseNormalizationMultiplicity_finite pm

theorem baseOrbicurvePresentation_coarseScheme (pm : Bool) :
    (S.baseOrbicurvePresentation pm).coarseScheme = S.baseNormalizationScheme pm := rfl

@[instance_reducible] def signedBaseNormalizationAlgebra :
    Algebra (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
  Genuine.signedNormalizationAlgebra S.prime.EK 1 ⊥

attribute [local instance] signedBaseNormalizationAlgebra

theorem signedBaseNormalization_ramificationCondition
    (w : Ideal (S.baseNormalizationRing false)) (hw : w.IsMaximal) :
    (letI := S.signedBaseNormalizationRingMap.toRingHom.toAlgebra;
      w.ramificationIdx (S.baseNormalizationRing true)) * S.baseNormalizationMultiplicity false w =
        S.baseNormalizationMultiplicity true (w.comap S.signedBaseNormalizationRingMap) := by
  have : w.IsMaximal := hw
  let v := w.comap S.signedBaseNormalizationRingMap
  have : w.LiesOver v := ⟨rfl⟩
  exact (mul_one _).trans
    (Genuine.signedNormalizationMultiplicity_eq_ramificationIdx S.prime.EK 1 ⊥ v w).symm

def signedBaseOrbicurvePresentation :
    AffineOrbicurvePresentation.Cover
      (S.baseOrbicurvePresentation false) (S.baseOrbicurvePresentation true) where
  f := S.signedBaseNormalizationRingMap
  injective := Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥
  isIntegral := Genuine.signedNormalizationRingMap_isIntegral S.prime.EK 1 ⊥
  ramification := S.signedBaseNormalization_ramificationCondition

theorem signedBaseOrbicurvePresentation_coarseMap :
    S.signedBaseOrbicurvePresentation.coarseMap = S.signedBaseNormalizationMap := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
