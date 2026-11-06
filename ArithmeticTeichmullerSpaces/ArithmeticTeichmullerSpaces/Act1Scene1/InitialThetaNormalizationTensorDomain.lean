import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationTensorInjective
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedLinearDisjoint
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationTensor

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZATION-TENSOR-DOMAIN
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual signed/base linear disjointness and finite normalization.
fidelity: the original seed's normalization tensor map is injective. Its
entire tensor ring is a domain with the actual unsigned covering field as
fraction field. The previous selected component is the whole tensor scheme,
and the finite normalization is birational over that scheme's identity.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived. The tensor ring is not proved normal, and the
normalization ring map is not proved surjective. Orbicurve realization,
the Cartesian covering law and the full geometry producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] coverTensorBaseAlgebra coverTensorBaseSMul coverTensorBaseModule
  baseTensorBaseAlgebra baseTensorBaseSMul baseTensorBaseModule
  normalizationTensorCommRing tensorRingBaseAlgebra normalizationTensorBase_xLineSMul
  normalizationFieldTensorBaseAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem normalizationTensorMap_injective : Function.Injective S.normalizationTensorMap :=
  FunctionFieldNormalization.normalizationTensorMap_injective_of_linearDisjoint
    (Genuine.transcendental_xG S.prime.EK)
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalizationFields_signed_linearDisjoint S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationTensorMap_ker_eq_bot :
    RingHom.ker S.normalizationTensorMap.toRingHom = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot S.normalizationTensorMap.toRingHom).mp
    S.normalizationTensorMap_injective

theorem normalizationTensorFieldMap_ker_eq_bot :
    RingHom.ker S.normalizationTensorFieldMap.toRingHom = ⊥ :=
  S.normalizationTensorKernel_eq.trans S.normalizationTensorMap_ker_eq_bot

theorem normalizationTensorFieldMap_injective :
    Function.Injective S.normalizationTensorFieldMap :=
  (RingHom.injective_iff_ker_eq_bot S.normalizationTensorFieldMap.toRingHom).mpr
    S.normalizationTensorFieldMap_ker_eq_bot

instance normalizationTensorRing_isDomain : IsDomain S.normalizationTensorRing :=
  S.normalizationTensorFieldMap_injective.isDomain S.normalizationTensorFieldMap.toRingHom

@[instance_reducible] def normalizationTensorFieldAlgebra :
    Algebra S.normalizationTensorRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  S.normalizationTensorFieldMap.toRingHom.toAlgebra

theorem normalizationTensor_fractionField :
    letI := S.normalizationTensorFieldAlgebra
    IsFractionRing S.normalizationTensorRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) := by
  letI := S.normalizationTensorFieldAlgebra
  apply FunctionFieldNormalization.fractionRing_of_fieldClosure
    S.normalizationTensorFieldMap_injective
  change Subfield.closure (Set.range S.normalizationTensorFieldMap) = ⊤
  exact FunctionFieldNormalization.normalizationTensorFieldMap_fieldClosure
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)
    S.normalizationFieldCover_unsigned_eq_sup.symm

instance isIso_tensorComponentToTensorScheme : IsIso S.tensorComponentToTensorScheme :=
  isIso_SpecMap_iff.mpr
    ((Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr S.normalizationTensorMap_ker_eq_bot)

theorem normalizationToTensorScheme_birationalOver :
    Scheme.BirationalOver S.normalizationToTensorScheme
      (𝟙 S.normalizationTensorScheme) := by
  let T := S.normalizationTensorRing
  let B := S.coverNormalizationRing false
  let N := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false
  letI : Algebra T B := S.normalizationTensorMap.toRingHom.toAlgebra
  letI : Algebra T N := S.normalizationTensorFieldAlgebra
  letI : IsScalarTower T B N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing T N := S.normalizationTensor_fractionField
  haveI : Module.Finite T B := S.normalizationTensorMap_finite
  have h := finite_extension_birationalOver (R := T) (A := B) (K := N)
    Subtype.val_injective (𝟙 S.normalizationTensorScheme)
  change Scheme.BirationalOver
    (S.normalizationToTensorScheme ≫ 𝟙 S.normalizationTensorScheme)
    (𝟙 S.normalizationTensorScheme) at h
  simpa only [Category.comp_id] using h

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
