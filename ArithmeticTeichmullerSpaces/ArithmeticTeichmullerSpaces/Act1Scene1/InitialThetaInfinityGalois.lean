import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFiber
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedGalois
import Mathlib.RingTheory.IsGaloisGroup.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-INFINITY-SIGNED-GALOIS-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the same signed field quotient restricted to the inverse-coordinate chart.
fidelity: the original signed quotient acts on the new actual integral closure.
Its action agrees with the original field action, and its fixed ring is the
actual signed normalization ring in this chart. The field Galois law is the
proved relative signed/unsigned law; no Galois law over the rational base is assumed.
Original proofs; no reference implementation copied.
boundary: this is the ring action needed for the boundary orbit quotient.
Torsion-cusp, distinguished epsilon, geometric stabilizers and the complete
geometry producer are separate identifications.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityNormalizationField_field infinityNormalizationField_rationalBaseAlgebra
  infinityNormalizationField_baseAlgebra infinityNormalizationField_baseSMul
  infinityNormalizationField_baseModule infinityNormalizationField_coefficientAlgebra
  infinityNormalizationField_coefficientSMul infinityNormalizationField_coefficientModule
  infinityNormalizationField_coefficientBaseTower infinityNormalizationField_baseTower
  infinityNormalizationRing_baseAlgebra infinityNormalizationRing_baseSMul
  infinityNormalizationRing_baseModule infinityNormalizationRing_coefficientAlgebra
  infinityNormalizationRing_isDedekindDomain infinityNormalizationRing_finite
  infinityNormalizationRing_fractionField

attribute [local instance] signedCoverFieldAlgebra

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The same signed field inclusion, with the inverse-coordinate field names. -/
@[instance_reducible] def infinitySignedFieldAlgebra :
    Algebra (S.infinityNormalizationField true) (S.infinityNormalizationField false) :=
  S.signedCoverFieldAlgebra

attribute [local instance] infinitySignedFieldAlgebra

local instance infinitySignedFieldSMul :
    SMul (S.infinityNormalizationField true) (S.infinityNormalizationField false) :=
  S.infinitySignedFieldAlgebra.toSMul

local instance infinitySignedFieldModule :
    Module (S.infinityNormalizationField true) (S.infinityNormalizationField false) :=
  S.infinitySignedFieldAlgebra.toModule

local instance infinitySignedFieldBaseTower :
    IsScalarTower S.infinityPolynomialBase (S.infinityNormalizationField true)
      (S.infinityNormalizationField false) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The original signed quotient action on the same ambient unsigned subfield. -/
def infinitySignedFieldAut : S.signedCoverQuotientGroup →*
    (S.infinityNormalizationField false ≃ₐ[S.infinityNormalizationField true]
      S.infinityNormalizationField false) :=
  S.signedCoverQuotientFieldAut

theorem infinitySignedFieldAut_eq_original (g : S.signedCoverQuotientGroup)
    (x : S.infinityNormalizationField false) :
    S.infinitySignedFieldAut g x = S.signedCoverQuotientFieldAut g x := rfl

/-- Use the original quotient homomorphism with the inverse-coordinate field types. -/
@[instance_reducible] def infinitySignedFieldAction :
    MulSemiringAction S.signedCoverQuotientGroup (S.infinityNormalizationField false) :=
  MulSemiringAction.compHom _ S.infinitySignedFieldAut

attribute [local instance] infinitySignedFieldAction

local instance infinitySignedFieldActionSMul :
    SMul S.signedCoverQuotientGroup (S.infinityNormalizationField false) :=
  S.infinitySignedFieldAction.toDistribMulAction.toMulAction.toSMul

/-- Rebase preserves the already proved relative field Galois law. -/
theorem infinitySignedFieldGaloisGroup :
    IsGaloisGroup S.signedCoverQuotientGroup
      (S.infinityNormalizationField true) (S.infinityNormalizationField false) :=
  Genuine.signedFieldGaloisGroup S.prime.EK S.prime.ℓ S.prime.M

local instance infinityFieldBaseComm :
    SMulCommClass S.signedCoverQuotientGroup S.infinityPolynomialBase
      (S.infinityNormalizationField false) where
  smul_comm g a b := by
    change S.infinitySignedFieldAut g
        (algebraMap S.infinityPolynomialBase (S.infinityNormalizationField false) a * b) =
      algebraMap S.infinityPolynomialBase (S.infinityNormalizationField false) a *
        S.infinitySignedFieldAut g b
    exact (map_mul (S.infinitySignedFieldAut g) _ _).trans
      (congrArg (fun z => z * S.infinitySignedFieldAut g b)
        ((S.infinitySignedFieldAut g).commutes
          (algebraMap S.infinityPolynomialBase (S.infinityNormalizationField true) a)))

/-- Restrict the same field action to the actual inverse-coordinate integral closure. -/
@[instance_reducible] def infinitySignedNormalizationAction :
    MulSemiringAction S.signedCoverQuotientGroup (S.infinityNormalizationRing false) :=
  inferInstance

attribute [local instance] infinitySignedNormalizationAction

local instance infinitySignedNormalizationActionSMul :
    SMul S.signedCoverQuotientGroup (S.infinityNormalizationRing false) :=
  S.infinitySignedNormalizationAction.toDistribMulAction.toMulAction.toSMul

theorem coe_infinitySignedNormalizationAction (g : S.signedCoverQuotientGroup)
    (a : S.infinityNormalizationRing false) :
    ((g • a : S.infinityNormalizationRing false) : S.infinityNormalizationField false) =
      S.infinitySignedFieldAut g (a : S.infinityNormalizationField false) := rfl

/-- The algebra on the two new rings is exactly the original infinity-chart ring map. -/
@[instance_reducible] def infinitySignedRingAlgebra :
    Algebra (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinityNormalizationRingMap.toRingHom.toAlgebra

attribute [local instance] infinitySignedRingAlgebra

local instance infinitySignedRingSMul :
    SMul (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinitySignedRingAlgebra.toSMul

local instance infinitySignedRingModule :
    Module (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinitySignedRingAlgebra.toModule

local instance infinitySignedRingFieldAlgebra :
    Algebra (S.infinityNormalizationRing true) (S.infinityNormalizationField false) :=
  ((algebraMap (S.infinityNormalizationField true) (S.infinityNormalizationField false)).comp
    (algebraMap (S.infinityNormalizationRing true) (S.infinityNormalizationField true))).toAlgebra

local instance infinitySignedRingFieldSMul :
    SMul (S.infinityNormalizationRing true) (S.infinityNormalizationField false) :=
  S.infinitySignedRingFieldAlgebra.toSMul

local instance infinitySignedRingFieldModule :
    Module (S.infinityNormalizationRing true) (S.infinityNormalizationField false) :=
  S.infinitySignedRingFieldAlgebra.toModule

local instance infinitySignedFractionTower :
    IsScalarTower (S.infinityNormalizationRing true) (S.infinityNormalizationField true)
      (S.infinityNormalizationField false) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance infinitySignedRingFractionTower :
    IsScalarTower (S.infinityNormalizationRing true) (S.infinityNormalizationRing false)
      (S.infinityNormalizationField false) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance infinityNormalizationAction_distrib :
    SMulDistribClass S.signedCoverQuotientGroup (S.infinityNormalizationRing false)
      (S.infinityNormalizationField false) := inferInstance

theorem infinityNormalizationRingMap_isIntegral :
    S.infinityNormalizationRingMap.toRingHom.IsIntegral :=
  FunctionFieldNormalization.ringMap_isIntegral _

local instance infinitySignedRingIntegral :
    Algebra.IsIntegral (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  ⟨S.infinityNormalizationRingMap_isIntegral⟩

/-- The same quotient is the Galois group of the actual new normalization inclusion. -/
theorem infinitySignedNormalizationGaloisGroup :
    IsGaloisGroup S.signedCoverQuotientGroup
      (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) := by
  have := S.infinitySignedFieldGaloisGroup
  exact IsGaloisGroup.of_isFractionRing S.signedCoverQuotientGroup
    (S.infinityNormalizationRing true) (S.infinityNormalizationRing false)
    (S.infinityNormalizationField true) (S.infinityNormalizationField false)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
