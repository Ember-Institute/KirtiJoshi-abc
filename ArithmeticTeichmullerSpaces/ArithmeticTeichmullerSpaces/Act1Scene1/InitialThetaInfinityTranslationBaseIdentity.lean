import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationBase
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineFullTorsionBaseField

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the seed's actual full rational torsion cardinality and the resulting
equality with the level-one unsigned elliptic function field.
fidelity: the existing lower inverse-coordinate field is literally the
level-one unsigned field rebased to the same inverse-coordinate rational line.
boundary: the unique infinity prime and a torsion-boundary equivalence remain
separate proofs.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityTranslationBaseField_field infinityTranslationBaseField_rationalAlgebra
  infinityTranslationBaseField_baseAlgebra infinityTranslationBaseField_baseSMul
  infinityTranslationBaseField_baseModule infinityTranslationBaseField_coefficientAlgebra
  infinityTranslationBaseField_baseTower infinityTranslationBaseField_coefficientTower
  infinityTranslationBaseRing_baseAlgebra infinityTranslationBaseRing_baseSMul
  infinityTranslationBaseRing_baseModule infinityTranslationBaseRing_coefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem fullTorsionTranslationField_eq_levelOne :
    Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.TK false =
      Genuine.stabilizerField S.prime.EK 1 ⊥ false :=
  Genuine.stabilizerField_fullTorsion_false_eq_levelOne S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.card_TK

/-- The actual level-one elliptic function field in the existing infinity chart. -/
def infinityTranslationLevelOneField :
    IntermediateField
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (Genuine.Ω S.prime.EK) :=
  rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.normalizationField S.prime.EK 1 ⊥ false)

/-- The existing lower field is exactly the original level-one elliptic field in this chart. -/
theorem infinityTranslationBaseField_eq_elliptic :
    S.infinityTranslationBaseField =
      rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine
        (Genuine.normalizationField S.prime.EK 1 ⊥ false) := by
  have h := Genuine.normalizationField_fullTorsion_false_eq_levelOne S.prime.EK
    S.prime.ℓ S.prime.ℓ_prime.pos S.prime.card_TK
  unfold infinityTranslationBaseField
  rw [h]

theorem infinityTranslationBaseField_eq_levelOne :
    S.infinityTranslationBaseField = S.infinityTranslationLevelOneField :=
  S.infinityTranslationBaseField_eq_elliptic

/-- The same actual function-field embedding lands bijectively in the existing lower field. -/
def infinityTranslationBaseFunctionFieldEquiv :
    S.prime.EK.toAffine.FunctionField ≃+* S.infinityTranslationBaseField :=
  Genuine.fullTorsionBaseFunctionFieldEquiv S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.card_TK

@[simp] theorem coe_infinityTranslationBaseFunctionFieldEquiv
    (f : S.prime.EK.toAffine.FunctionField) :
    ((S.infinityTranslationBaseFunctionFieldEquiv f : S.infinityTranslationBaseField) :
      Genuine.Ω S.prime.EK) = Genuine.ιF S.prime.EK f :=
  Genuine.coe_fullTorsionBaseFunctionFieldEquiv S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.card_TK f

/-- The actual integral closure in the level-one elliptic field over the inverse chart. -/
abbrev infinityTranslationEllipticRing :=
  coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityTranslationLevelOneField

/-- The equality of fields induces the ambient-value-preserving normalization equivalence. -/
def infinityTranslationBaseRingEquivElliptic :
    S.infinityTranslationBaseRing ≃+* S.infinityTranslationEllipticRing :=
  coordRingEquivOfEq S.infinityTranslationBaseField_eq_levelOne

@[simp] theorem coe_infinityTranslationBaseRingEquivElliptic
    (a : S.infinityTranslationBaseRing) :
    (((S.infinityTranslationBaseRingEquivElliptic a : S.infinityTranslationEllipticRing) :
      S.infinityTranslationLevelOneField) : Genuine.Ω S.prime.EK) =
        ((a : S.infinityTranslationBaseField) : Genuine.Ω S.prime.EK) :=
  coe_coordRingEquivOfEq S.infinityTranslationBaseField_eq_levelOne a

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
