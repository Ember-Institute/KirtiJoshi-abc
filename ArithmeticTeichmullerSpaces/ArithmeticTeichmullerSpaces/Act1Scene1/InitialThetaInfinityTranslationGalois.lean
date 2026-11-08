import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationBase
import Mathlib.RingTheory.IsGaloisGroup.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the proved actual translation quotient field action and integral-closure restriction.
fidelity: the same original quotient acts on the existing unsigned infinity
normalization ring over the actual full-TK lower ring. The action has the same
ambient values as the original field action and the proved relative Galois law.
boundary: Scene1/Derived; no torsion-boundary equivalence, trivial inertia,
singleton lower fiber, or AG cusp identity is assumed or asserted.
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
  infinityNormalizationField_field infinityNormalizationField_rationalBaseAlgebra
  infinityNormalizationField_baseAlgebra infinityNormalizationField_baseSMul
  infinityNormalizationField_baseModule infinityNormalizationField_coefficientAlgebra
  infinityNormalizationField_coefficientSMul infinityNormalizationField_coefficientModule
  infinityNormalizationField_coefficientBaseTower infinityNormalizationField_baseTower
  infinityNormalizationRing_baseAlgebra infinityNormalizationRing_baseSMul
  infinityNormalizationRing_baseModule infinityNormalizationRing_coefficientAlgebra
  infinityNormalizationRing_isDedekindDomain infinityNormalizationRing_finite
  infinityNormalizationRing_fractionField

attribute [local instance] infinityTranslationBaseField_field
  infinityTranslationBaseField_rationalAlgebra infinityTranslationBaseField_baseAlgebra
  infinityTranslationBaseField_baseSMul infinityTranslationBaseField_baseModule
  infinityTranslationBaseField_coefficientAlgebra infinityTranslationBaseField_baseTower
  infinityTranslationBaseField_coefficientTower infinityTranslationBaseRing_baseAlgebra
  infinityTranslationBaseRing_baseSMul infinityTranslationBaseRing_baseModule
  infinityTranslationBaseRing_coefficientAlgebra

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance infinityTranslationNormal :
    ((Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.M false).subgroupOf
      (Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false)).Normal :=
  S.functionFieldCoverGroup_translation_normal

/-- Keep exactly the original translation quotient as acting group. -/
abbrev infinityTranslationGroup :=
  Genuine.torsionTranslationGaloisGroup S.prime.EK S.prime.ℓ S.prime.TK S.prime.M

instance finite_infinityTranslationGroup : Finite S.infinityTranslationGroup :=
  Genuine.finite_torsionTranslationGaloisGroup S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.TK le_rfl S.prime.M S.prime.M_le_TK

/-- Use the original relative field inclusion on the same actual subfields. -/
@[instance_reducible] def infinityTranslationFieldAlgebra :
    Algebra S.infinityTranslationBaseField (S.infinityNormalizationField false) :=
  Genuine.torsionTranslationFieldAlgebra S.prime.EK S.prime.ℓ
    S.prime.TK S.prime.M S.prime.M_le_TK

attribute [local instance] infinityTranslationFieldAlgebra

@[instance_reducible] def infinityTranslationFieldSMul :
    SMul S.infinityTranslationBaseField (S.infinityNormalizationField false) :=
  S.infinityTranslationFieldAlgebra.toSMul

@[instance_reducible] def infinityTranslationFieldModule :
    Module S.infinityTranslationBaseField (S.infinityNormalizationField false) :=
  S.infinityTranslationFieldAlgebra.toModule

attribute [local instance] infinityTranslationFieldSMul infinityTranslationFieldModule

local instance infinityTranslationPolynomialFieldTower :
    IsScalarTower S.infinityPolynomialBase S.infinityTranslationBaseField
      (S.infinityNormalizationField false) := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The original field automorphisms, on the original unsigned infinity field. -/
def infinityTranslationFieldAut : S.infinityTranslationGroup →*
    (S.infinityNormalizationField false ≃ₐ[S.infinityTranslationBaseField]
      S.infinityNormalizationField false) :=
  Genuine.torsionTranslationQuotientFieldAut S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.TK le_rfl S.prime.M S.prime.M_le_TK

/-- The field automorphism retains the original ambient automorphism on every representative. -/
theorem coe_infinityTranslationFieldAut_mk
    (g : Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false)
    (x : S.infinityNormalizationField false) :
    ((S.infinityTranslationFieldAut (QuotientGroup.mk g) x :
      S.infinityNormalizationField false) : Genuine.Ω S.prime.EK) = g.val x.val := rfl

/-- Restrict the same quotient homomorphism, without replacing its group carrier. -/
@[instance_reducible] def infinityTranslationFieldAction :
    MulSemiringAction S.infinityTranslationGroup (S.infinityNormalizationField false) :=
  MulSemiringAction.compHom _ S.infinityTranslationFieldAut

attribute [local instance] infinityTranslationFieldAction

@[instance_reducible] def infinityTranslationFieldActionSMul :
    SMul S.infinityTranslationGroup (S.infinityNormalizationField false) :=
  S.infinityTranslationFieldAction.toDistribMulAction.toMulAction.toSMul

attribute [local instance] infinityTranslationFieldActionSMul

/-- Relative Galois is already proved before rebasing the normalization chart. -/
theorem infinityTranslationFieldGaloisGroup :
    IsGaloisGroup S.infinityTranslationGroup S.infinityTranslationBaseField
      (S.infinityNormalizationField false) :=
  Genuine.torsionTranslationFieldGaloisGroup S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.TK le_rfl S.prime.M S.prime.M_le_TK

@[instance_reducible] def infinityTranslationFieldBaseComm :
    SMulCommClass S.infinityTranslationGroup S.infinityPolynomialBase
      (S.infinityNormalizationField false) where
  smul_comm g a b := by
    change S.infinityTranslationFieldAut g
        (algebraMap S.infinityPolynomialBase (S.infinityNormalizationField false) a * b) =
      algebraMap S.infinityPolynomialBase (S.infinityNormalizationField false) a *
        S.infinityTranslationFieldAut g b
    exact (map_mul (S.infinityTranslationFieldAut g) _ _).trans
      (congrArg (fun z => z * S.infinityTranslationFieldAut g b)
        ((S.infinityTranslationFieldAut g).commutes
          (algebraMap S.infinityPolynomialBase S.infinityTranslationBaseField a)))

attribute [local instance] infinityTranslationFieldBaseComm

/-- The original action restricts to the actual upper integral closure. -/
@[instance_reducible] def infinityTranslationNormalizationAction :
    MulSemiringAction S.infinityTranslationGroup (S.infinityNormalizationRing false) :=
  inferInstance

attribute [local instance] infinityTranslationNormalizationAction

@[instance_reducible] def infinityTranslationNormalizationSMul :
    SMul S.infinityTranslationGroup (S.infinityNormalizationRing false) :=
  S.infinityTranslationNormalizationAction.toDistribMulAction.toMulAction.toSMul

attribute [local instance] infinityTranslationNormalizationSMul

/-- Evaluation in the fraction field is exactly the original field action. -/
theorem coe_infinityTranslationNormalizationAction (g : S.infinityTranslationGroup)
    (a : S.infinityNormalizationRing false) :
    ((g • a : S.infinityNormalizationRing false) : S.infinityNormalizationField false) =
      S.infinityTranslationFieldAut g (a : S.infinityNormalizationField false) := rfl

/-- The ring action has precisely the same ambient values as the original quotient action. -/
theorem coe_infinityTranslationNormalizationAction_mk
    (g : Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false)
    (a : S.infinityNormalizationRing false) :
    (((QuotientGroup.mk g : S.infinityTranslationGroup) • a :
      S.infinityNormalizationRing false) : S.infinityNormalizationField false).val =
        g.val a.val.val := rfl

/-- Fix the exact existing lower-to-upper normalization map as the ring algebra. -/
@[instance_reducible] def infinityTranslationRingAlgebra :
    Algebra S.infinityTranslationBaseRing (S.infinityNormalizationRing false) :=
  S.infinityTranslationRingMap.toRingHom.toAlgebra

attribute [local instance] infinityTranslationRingAlgebra

@[instance_reducible] def infinityTranslationRingSMul :
    SMul S.infinityTranslationBaseRing (S.infinityNormalizationRing false) :=
  S.infinityTranslationRingAlgebra.toSMul

@[instance_reducible] def infinityTranslationRingModule :
    Module S.infinityTranslationBaseRing (S.infinityNormalizationRing false) :=
  S.infinityTranslationRingAlgebra.toModule

attribute [local instance] infinityTranslationRingSMul infinityTranslationRingModule

local instance infinityTranslationRingFieldAlgebra :
    Algebra S.infinityTranslationBaseRing (S.infinityNormalizationField false) :=
  ((algebraMap S.infinityTranslationBaseField (S.infinityNormalizationField false)).comp
    (algebraMap S.infinityTranslationBaseRing S.infinityTranslationBaseField)).toAlgebra

local instance infinityTranslationRingFieldSMul :
    SMul S.infinityTranslationBaseRing (S.infinityNormalizationField false) :=
  S.infinityTranslationRingFieldAlgebra.toSMul

local instance infinityTranslationRingFieldModule :
    Module S.infinityTranslationBaseRing (S.infinityNormalizationField false) :=
  S.infinityTranslationRingFieldAlgebra.toModule

local instance infinityTranslationFractionTower :
    IsScalarTower S.infinityTranslationBaseRing S.infinityTranslationBaseField
      (S.infinityNormalizationField false) := IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance infinityTranslationRingFractionTower :
    IsScalarTower S.infinityTranslationBaseRing (S.infinityNormalizationRing false)
      (S.infinityNormalizationField false) := IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance infinityTranslationNormalizationAction_distrib :
    SMulDistribClass S.infinityTranslationGroup (S.infinityNormalizationRing false)
      (S.infinityNormalizationField false) := inferInstance

local instance infinityTranslationRingIntegral :
    Algebra.IsIntegral S.infinityTranslationBaseRing (S.infinityNormalizationRing false) :=
  ⟨S.infinityTranslationRingMap_isIntegral⟩

/-- The same original quotient is the Galois group of the actual infinity-ring inclusion. -/
theorem infinityTranslationNormalizationGaloisGroup :
    IsGaloisGroup S.infinityTranslationGroup S.infinityTranslationBaseRing
      (S.infinityNormalizationRing false) := by
  have := S.infinityTranslationFieldGaloisGroup
  exact IsGaloisGroup.of_isFractionRing S.infinityTranslationGroup
    S.infinityTranslationBaseRing (S.infinityNormalizationRing false)
    S.infinityTranslationBaseField (S.infinityNormalizationField false)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
