import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationTensorField
import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteBirationalLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedCompositum
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual normalization inclusions and the proved unsigned compositum identity.
fidelity: constructs the same seed's tensor map from its signed covering ring
and unsigned base ring. Its image has the original unsigned covering field as
fraction field, and the original unsigned ring is the image's integral closure.
The tensor map is finite and selects a minimal prime of the tensor algebra.
boundary: Scene1/Derived. This is the finite normalization of the selected
ordinary tensor component. The orbicurve cartesian law remains open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

abbrev normalizationTensorBase :=
  FunctionFieldNormalization.polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)

local instance coverTensorBaseAlgebra (pm : Bool) :
    Algebra S.normalizationTensorBase (S.coverNormalizationRing pm) :=
  FunctionFieldNormalization.coordRingBaseAlgebra
    (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M pm)
local instance coverTensorBaseSMul (pm : Bool) :
    SMul S.normalizationTensorBase (S.coverNormalizationRing pm) :=
  (coverTensorBaseAlgebra S pm).toSMul
local instance coverTensorBaseModule (pm : Bool) :
    Module S.normalizationTensorBase (S.coverNormalizationRing pm) :=
  (coverTensorBaseAlgebra S pm).toModule
local instance baseTensorBaseAlgebra :
    Algebra S.normalizationTensorBase (S.baseNormalizationRing false) :=
  FunctionFieldNormalization.coordRingBaseAlgebra
    (Genuine.normalizationField S.prime.EK 1 ⊥ false)
local instance baseTensorBaseSMul :
    SMul S.normalizationTensorBase (S.baseNormalizationRing false) :=
  (baseTensorBaseAlgebra S).toSMul
local instance baseTensorBaseModule :
    Module S.normalizationTensorBase (S.baseNormalizationRing false) :=
  (baseTensorBaseAlgebra S).toModule

def normalizationTensorRing :=
  S.coverNormalizationRing true ⊗[S.normalizationTensorBase] S.baseNormalizationRing false

local instance normalizationTensorCommRing : CommRing S.normalizationTensorRing :=
  { (Algebra.TensorProduct.instCommRing : CommRing S.normalizationTensorRing) with
    toSemiring := (Algebra.TensorProduct.instSemiring : Semiring S.normalizationTensorRing) }

local instance tensorRingBaseAlgebra : Algebra S.normalizationTensorBase S.normalizationTensorRing :=
  (Algebra.TensorProduct.instAlgebra : Algebra S.normalizationTensorBase S.normalizationTensorRing)

local instance normalizationTensorBase_xLineSMul :
    SMul S.normalizationTensorBase (Genuine.xLine S.prime.EK) :=
  (show Algebra S.normalizationTensorBase (Genuine.xLine S.prime.EK) from inferInstance).toSMul

local instance normalizationFieldTensorBaseAlgebra :
    Algebra S.normalizationTensorBase
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  IntermediateField.algebra' _

def normalizationTensorMap : S.normalizationTensorRing →ₐ[S.normalizationTensorBase]
    S.coverNormalizationRing false :=
  FunctionFieldNormalization.normalizationTensorMap
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationTensorMap_tmul
    (a : S.coverNormalizationRing true) (b : S.baseNormalizationRing false) :
    S.normalizationTensorMap (a ⊗ₜ b) =
      S.signedCoverNormalizationRingMap a * S.baseToCoverNormalizationRingMap false b := rfl

def normalizationTensorFieldMap : S.normalizationTensorRing →ₐ[S.normalizationTensorBase]
    Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false :=
  FunctionFieldNormalization.normalizationTensorFieldMap
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem unsignedNormalization_isIntegralClosure_tensor :
    letI := S.normalizationTensorFieldMap.toRingHom.toAlgebra
    IsIntegralClosure (S.coverNormalizationRing false) S.normalizationTensorRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  FunctionFieldNormalization.normalizationTensor_isIntegralClosure
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationTensorImage_fractionField :
    IsFractionRing S.normalizationTensorFieldMap.range
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  FunctionFieldNormalization.normalizationTensorImage_fractionField
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)
    S.normalizationFieldCover_unsigned_eq_sup.symm

theorem unsignedNormalization_isIntegralClosure_tensorImage :
    IsIntegralClosure (S.coverNormalizationRing false) S.normalizationTensorFieldMap.range
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  FunctionFieldNormalization.normalizationTensorImage_isIntegralClosure
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationTensorMap_finite :
    RingHom.Finite (A := S.normalizationTensorRing) (B := S.coverNormalizationRing false)
      S.normalizationTensorMap.toRingHom :=
  FunctionFieldNormalization.normalizationTensorMap_finite (Genuine.transcendental_xG S.prime.EK)
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationTensorKernel_eq :
    RingHom.ker S.normalizationTensorFieldMap.toRingHom =
      RingHom.ker S.normalizationTensorMap.toRingHom := by
  ext x
  change ((S.normalizationTensorMap x : S.coverNormalizationRing false) :
    Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) = 0 ↔
      S.normalizationTensorMap x = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem normalizationTensorKernel_minimalPrime :
    RingHom.ker S.normalizationTensorMap.toRingHom ∈
      (⊥ : Ideal S.normalizationTensorRing).minimalPrimes := by
  have hq : (RingHom.ker S.normalizationTensorFieldMap.toRingHom).under
      S.normalizationTensorBase = ⊥ := by
    ext a
    change S.normalizationTensorFieldMap (algebraMap S.normalizationTensorBase S.normalizationTensorRing a) = 0 ↔ a = 0
    rw [AlgHom.commutes]
    constructor
    · intro h
      exact (FaithfulSMul.algebraMap_injective S.normalizationTensorBase
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false))
          (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  have hqmem : RingHom.ker S.normalizationTensorFieldMap.toRingHom ∈
      (⊥ : Ideal S.normalizationTensorRing).minimalPrimes := by
    letI : Algebra S.normalizationTensorBase S.normalizationTensorRing := S.tensorRingBaseAlgebra
    letI : SMul S.normalizationTensorBase S.normalizationTensorRing :=
      S.tensorRingBaseAlgebra.toSMul
    letI : Module S.normalizationTensorBase S.normalizationTensorRing :=
      S.tensorRingBaseAlgebra.toModule
    letI : Algebra S.normalizationTensorBase
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
      S.normalizationFieldTensorBaseAlgebra
    letI : SMul S.normalizationTensorBase
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
      S.normalizationFieldTensorBaseAlgebra.toSMul
    letI : Algebra S.normalizationTensorRing
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
      S.normalizationTensorFieldMap.toRingHom.toAlgebra
    letI : IsScalarTower S.normalizationTensorBase S.normalizationTensorRing
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (S.normalizationTensorFieldMap.commutes a).symm
    letI : Algebra.IsIntegral S.normalizationTensorBase S.normalizationTensorRing :=
      FunctionFieldNormalization.normalizationTensor_integral
        (F := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M true)
        (Z := Genuine.normalizationField S.prime.EK 1 ⊥ false)
    letI : (RingHom.ker S.normalizationTensorFieldMap.toRingHom).IsPrime :=
      RingHom.ker_isPrime _
    have h := Ideal.IsIntegral.mem_minimalPrimes_map_under
      (R := S.normalizationTensorBase)
        (RingHom.ker S.normalizationTensorFieldMap.toRingHom)
    simpa only [hq, Ideal.map_bot] using h
  exact S.normalizationTensorKernel_eq ▸ hqmem

def normalizationTensorScheme : Scheme := Spec (CommRingCat.of S.normalizationTensorRing)

def normalizationToTensorScheme : S.coverNormalizationScheme false ⟶ S.normalizationTensorScheme :=
  Spec.map (CommRingCat.ofHom S.normalizationTensorMap.toRingHom)

instance finite_normalizationToTensorScheme : IsFinite S.normalizationToTensorScheme :=
  (IsFinite.SpecMap_iff _).mpr S.normalizationTensorMap_finite

abbrev normalizationTensorComponentRing :=
  S.normalizationTensorRing ⧸ RingHom.ker S.normalizationTensorMap.toRingHom

def normalizationTensorComponentRangeEquiv :
    S.normalizationTensorComponentRing ≃+*
      (S.normalizationTensorMap.toRingHom.range) :=
  RingHom.quotientKerEquivRange S.normalizationTensorMap.toRingHom

theorem normalizationTensorComponentRangeEquiv_apply_quotient (x : S.normalizationTensorRing) :
    S.normalizationTensorComponentRangeEquiv
        (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom) x) =
      ⟨S.normalizationTensorMap.toRingHom x, ⟨x, rfl⟩⟩ := rfl

instance normalizationTensorComponentRing_isDomain :
    IsDomain S.normalizationTensorComponentRing := by
  letI : (RingHom.ker S.normalizationTensorMap.toRingHom).IsPrime :=
    Ideal.IsMinimalPrime.isPrime S.normalizationTensorKernel_minimalPrime
  exact Ideal.Quotient.isDomain _

def normalizationTensorComponentScheme : Scheme :=
  Spec (CommRingCat.of S.normalizationTensorComponentRing)

instance affine_normalizationTensorComponentScheme :
    IsAffine S.normalizationTensorComponentScheme := by
  unfold normalizationTensorComponentScheme
  infer_instance

def tensorComponentToTensorScheme : S.normalizationTensorComponentScheme ⟶
    S.normalizationTensorScheme :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom)))

instance finite_tensorComponentToTensorScheme :
    IsFinite S.tensorComponentToTensorScheme :=
  (IsFinite.SpecMap_iff _).mpr
    (RingHom.Finite.of_surjective
      (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom))
      (Ideal.Quotient.mk_surjective))

theorem tensorComponentQuotientRingMap_isIntegral :
    (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom)).IsIntegral :=
  RingHom.IsIntegral.of_finite
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

instance closedImmersion_tensorComponentToTensorScheme :
    IsClosedImmersion S.tensorComponentToTensorScheme :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

def normalizationToTensorComponentRingMap :
    S.normalizationTensorComponentRing →+* S.coverNormalizationRing false :=
  Ideal.Quotient.lift (RingHom.ker S.normalizationTensorMap.toRingHom)
    S.normalizationTensorMap.toRingHom (fun _ h => h)

theorem normalizationToTensorComponentRingMap_range :
    S.normalizationToTensorComponentRingMap.range =
      S.normalizationTensorMap.toRingHom.range :=
  FunctionFieldNormalization.quotientLift_range_eq S.normalizationTensorMap.toRingHom

def normalizationTensorComponentFieldMap :
    S.normalizationTensorComponentRing →+*
      Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false :=
  Ideal.Quotient.lift (RingHom.ker S.normalizationTensorMap.toRingHom)
    S.normalizationTensorFieldMap.toRingHom (fun x hx => by
      apply RingHom.mem_ker.mp
      rw [S.normalizationTensorKernel_eq]
      exact hx)

theorem normalizationTensorComponentFieldMap_apply_quotient (x : S.normalizationTensorRing) :
    S.normalizationTensorComponentFieldMap
        (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom) x) =
      S.normalizationTensorFieldMap x := by
  rfl

theorem normalizationTensorComponentFieldMap_range :
    S.normalizationTensorComponentFieldMap.range =
      S.normalizationTensorFieldMap.toRingHom.range := by
  exact FunctionFieldNormalization.quotientLift_range_eq_of_ker_eq
    S.normalizationTensorMap.toRingHom S.normalizationTensorFieldMap.toRingHom
      S.normalizationTensorKernel_eq.symm

theorem normalizationTensorComponentFieldMap_injective :
    Function.Injective S.normalizationTensorComponentFieldMap :=
  FunctionFieldNormalization.quotientLift_injective_of_ker_eq
    S.normalizationTensorMap.toRingHom S.normalizationTensorFieldMap.toRingHom
      S.normalizationTensorKernel_eq.symm

theorem normalizationTensorComponentFieldMap_ker_eq_bot :
    RingHom.ker S.normalizationTensorComponentFieldMap = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot S.normalizationTensorComponentFieldMap).mp
    S.normalizationTensorComponentFieldMap_injective

@[instance_reducible] def normalizationTensorComponentFieldAlgebra :
    Algebra S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  S.normalizationTensorComponentFieldMap.toAlgebra

theorem normalizationTensorComponentFieldMap_faithful :
    letI := S.normalizationTensorComponentFieldAlgebra
    FaithfulSMul S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) := by
  letI := S.normalizationTensorComponentFieldAlgebra
  exact (faithfulSMul_iff_algebraMap_injective _ _).mpr
    S.normalizationTensorComponentFieldMap_injective

theorem normalizationTensorComponent_fractionField :
    letI := S.normalizationTensorComponentFieldAlgebra
    IsFractionRing S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) := by
  letI := S.normalizationTensorComponentFieldAlgebra
  apply FunctionFieldNormalization.fractionRing_of_fieldClosure
    S.normalizationTensorComponentFieldMap_injective
  have hrange : Set.range S.normalizationTensorComponentFieldMap =
      Set.range S.normalizationTensorFieldMap := by
    ext x
    change x ∈ S.normalizationTensorComponentFieldMap.range ↔
      x ∈ S.normalizationTensorFieldMap.toRingHom.range
    rw [S.normalizationTensorComponentFieldMap_range]
  change Subfield.closure (Set.range S.normalizationTensorComponentFieldMap) = ⊤
  rw [hrange]
  exact FunctionFieldNormalization.normalizationTensorFieldMap_fieldClosure
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)
    S.normalizationFieldCover_unsigned_eq_sup.symm

theorem unsignedNormalization_isIntegralClosure_tensorComponent :
    letI := S.normalizationTensorComponentFieldAlgebra
    IsIntegralClosure (S.coverNormalizationRing false) S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) := by
  letI := S.normalizationTensorComponentFieldAlgebra
  letI : Algebra S.normalizationTensorRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
    S.normalizationTensorFieldMap.toRingHom.toAlgebra
  letI : Algebra S.normalizationTensorRing S.normalizationTensorComponentRing :=
    (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom)).toAlgebra
  letI : IsScalarTower S.normalizationTensorRing S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (S.normalizationTensorComponentFieldMap_apply_quotient a).symm
  letI : Algebra.IsIntegral S.normalizationTensorRing S.normalizationTensorComponentRing :=
    ⟨S.tensorComponentQuotientRingMap_isIntegral⟩
  letI : IsIntegralClosure (S.coverNormalizationRing false) S.normalizationTensorRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
    S.unsignedNormalization_isIntegralClosure_tensor
  exact IsIntegralClosure.tower_top (R := S.normalizationTensorRing)

def normalizationToTensorComponentScheme : S.coverNormalizationScheme false ⟶
    S.normalizationTensorComponentScheme :=
  Spec.map (CommRingCat.ofHom S.normalizationToTensorComponentRingMap)

theorem normalizationToTensorComponentRingMap_comp_quotientMap :
    S.normalizationToTensorComponentRingMap.comp
        (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom)) =
      S.normalizationTensorMap.toRingHom := by
  apply RingHom.ext
  intro x
  simp only [normalizationToTensorComponentRingMap, RingHom.coe_comp, Function.comp_apply]
  exact Ideal.Quotient.lift_mk
    (RingHom.ker S.normalizationTensorMap.toRingHom)
    S.normalizationTensorMap.toRingHom (fun _ h => h)

theorem normalizationToTensorComponentRingMap_finite :
    RingHom.Finite S.normalizationToTensorComponentRingMap := by
  let T := S.normalizationTensorRing
  let Q := S.normalizationTensorComponentRing
  let B := S.coverNormalizationRing false
  letI : Algebra T B := S.normalizationTensorMap.toRingHom.toAlgebra
  letI : Algebra Q B := S.normalizationToTensorComponentRingMap.toAlgebra
  letI : Algebra T Q :=
    (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom)).toAlgebra
  letI : IsScalarTower T Q B :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact congrArg (fun f : T →+* B => f a)
        S.normalizationToTensorComponentRingMap_comp_quotientMap
  haveI : Module.Finite T B := S.normalizationTensorMap_finite
  exact Module.Finite.of_restrictScalars_finite T Q B

theorem normalizationToTensorComponentRingMap_isIntegral :
    S.normalizationToTensorComponentRingMap.IsIntegral :=
  RingHom.IsIntegral.of_finite S.normalizationToTensorComponentRingMap_finite

theorem normalizationToTensorComponentRingMap_injective :
    Function.Injective S.normalizationToTensorComponentRingMap :=
  RingHom.lift_injective_of_ker_le_ideal
    (I := RingHom.ker S.normalizationTensorMap.toRingHom)
    (fun _ h => h) le_rfl

instance finite_normalizationToTensorComponentScheme :
    IsFinite S.normalizationToTensorComponentScheme :=
  (IsFinite.SpecMap_iff _).mpr S.normalizationToTensorComponentRingMap_finite

theorem normalizationToTensorComponentScheme_comp :
    S.normalizationToTensorComponentScheme ≫ S.tensorComponentToTensorScheme =
      S.normalizationToTensorScheme := by
  have h := congrArg (fun f : S.normalizationTensorRing →+* S.coverNormalizationRing false =>
      Spec.map (CommRingCat.ofHom f))
    S.normalizationToTensorComponentRingMap_comp_quotientMap
  exact (AlgebraicGeometry.Spec.map_comp
    (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker S.normalizationTensorMap.toRingHom)))
    (CommRingCat.ofHom S.normalizationToTensorComponentRingMap)).symm.trans h

instance surjective_normalizationToTensorComponentScheme :
    Surjective S.normalizationToTensorComponentScheme :=
  ⟨S.normalizationToTensorComponentRingMap_isIntegral.comap_surjective
    S.normalizationToTensorComponentRingMap_injective⟩

theorem normalizationTensorComponentFieldMap_eq_comp :
    S.normalizationTensorComponentFieldMap =
      (algebraMap (S.coverNormalizationRing false)
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false)).comp
          S.normalizationToTensorComponentRingMap :=
  Ideal.Quotient.ringHom_ext (RingHom.ext (fun _ => rfl))

theorem normalizationToTensorComponentScheme_birationalOver :
    Scheme.BirationalOver S.normalizationToTensorScheme S.tensorComponentToTensorScheme := by
  let Q := S.normalizationTensorComponentRing
  let B := S.coverNormalizationRing false
  let N := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false
  letI : Algebra Q B := S.normalizationToTensorComponentRingMap.toAlgebra
  letI : Algebra Q N := S.normalizationTensorComponentFieldAlgebra
  letI : IsScalarTower Q B N := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg (fun f : Q →+* N => f a) S.normalizationTensorComponentFieldMap_eq_comp
  haveI : IsFractionRing Q N := S.normalizationTensorComponent_fractionField
  haveI : Module.Finite Q B := S.normalizationToTensorComponentRingMap_finite
  have h := finite_extension_birationalOver (R := Q) (A := B) (K := N)
    Subtype.val_injective S.tensorComponentToTensorScheme
  change Scheme.BirationalOver
    (S.normalizationToTensorComponentScheme ≫ S.tensorComponentToTensorScheme)
    S.tensorComponentToTensorScheme at h
  rwa [S.normalizationToTensorComponentScheme_comp] at h

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
