import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFiber
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaTranslationFieldDegree

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the same seed's torsion-translation fixed fields and inverse-coordinate normalization.
fidelity: constructs the full-TK lower infinity chart and its inclusion into the
existing unsigned infinity chart. The original upper infinity fiber contracts
surjectively to the lower fiber. All fields retain their actual ambient values.
boundary: Scene1/Derived. This does not identify the boundary with torsion classes,
prove a singleton lower fiber, or supply an orbicurve cusp.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve Polynomial
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

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The actual inverse coordinate is transcendental. -/
theorem infinityTranslation_inverseCoordinate_transcendental :
    Transcendental ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹ := by
  intro h
  exact Genuine.transcendental_xG S.prime.EK
    ((IsAlgebraic.inv_iff (R := ↥S.prime.torsionField)
      (x := Genuine.xG S.prime.EK)).mp h)

/-- The inverse-coordinate line is the original x-line, as an actual subfield. -/
theorem infinityTranslation_xLine_eq_inverseCoordinateLine :
    Genuine.xLine S.prime.EK =
      rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹ := by
  change IntermediateField.adjoin ↥S.prime.torsionField {Genuine.xG S.prime.EK} =
    IntermediateField.adjoin ↥S.prime.torsionField {(Genuine.xG S.prime.EK)⁻¹}
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    have hu := IntermediateField.subset_adjoin ↥S.prime.torsionField
      {(Genuine.xG S.prime.EK)⁻¹} (Set.mem_singleton _)
    simpa using
      (IntermediateField.adjoin ↥S.prime.torsionField {(Genuine.xG S.prime.EK)⁻¹}).inv_mem hu
  · apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact (IntermediateField.adjoin ↥S.prime.torsionField {Genuine.xG S.prime.EK}).inv_mem
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))

/-- The original full-translation fixed field, in the inverse-coordinate naming. -/
def infinityTranslationBaseField :
    IntermediateField
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (Genuine.Ω S.prime.EK) :=
  rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.TK false)

@[instance_reducible] def infinityTranslationBaseField_field :
    Field S.infinityTranslationBaseField := S.infinityTranslationBaseField.toSubfield.toField

attribute [local instance] infinityTranslationBaseField_field

@[instance_reducible] def infinityTranslationBaseField_rationalAlgebra :
    Algebra (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityTranslationBaseField := IntermediateField.algebra' _

@[instance_reducible] def infinityTranslationBaseField_baseAlgebra :
    Algebra S.infinityPolynomialBase S.infinityTranslationBaseField :=
  IntermediateField.algebra' _

attribute [local instance] infinityTranslationBaseField_rationalAlgebra
  infinityTranslationBaseField_baseAlgebra

@[instance_reducible] def infinityTranslationBaseField_baseSMul :
    SMul S.infinityPolynomialBase S.infinityTranslationBaseField :=
  S.infinityTranslationBaseField_baseAlgebra.toSMul

@[instance_reducible] def infinityTranslationBaseField_baseModule :
    Module S.infinityPolynomialBase S.infinityTranslationBaseField :=
  S.infinityTranslationBaseField_baseAlgebra.toModule

@[instance_reducible] def infinityTranslationBaseField_coefficientAlgebra :
    Algebra ↥S.prime.torsionField S.infinityTranslationBaseField :=
  IntermediateField.algebra' _

attribute [local instance] infinityTranslationBaseField_baseSMul
  infinityTranslationBaseField_baseModule infinityTranslationBaseField_coefficientAlgebra

@[instance_reducible] def infinityTranslationBaseField_baseTower :
    IsScalarTower S.infinityPolynomialBase
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityTranslationBaseField := IsScalarTower.of_algebraMap_eq fun _ => rfl

@[instance_reducible] def infinityTranslationBaseField_coefficientTower :
    IsScalarTower ↥S.prime.torsionField S.infinityPolynomialBase
      S.infinityTranslationBaseField := IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] infinityTranslationBaseField_baseTower
  infinityTranslationBaseField_coefficientTower

instance finiteDimensional_infinityTranslationBaseField :
    FiniteDimensional
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityTranslationBaseField :=
  finiteDimensional_rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine _

instance separable_infinityTranslationBaseField :
    Algebra.IsSeparable
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityTranslationBaseField := by
  have : Algebra.IsAlgebraic
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityTranslationBaseField := Algebra.IsAlgebraic.of_finite _ _
  have : CharZero (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹) :=
    charZero_of_injective_algebraMap
      (algebraMap ↥S.prime.torsionField
        (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The original full-TK fixed field is contained in the original line fixed field. -/
theorem infinityTranslationBaseField_le :
    S.infinityTranslationBaseField ≤ S.infinityNormalizationField false := by
  intro x hx
  change x ∈ Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.TK false at hx
  change x ∈ Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.M false
  exact IntermediateField.fixedField_antitone
    (Genuine.Hgp_le S.prime.EK (n := 1) Nat.one_pos (one_mul S.prime.ℓ)
      (fun P hP => by simpa only [one_nsmul] using S.prime.M_le_TK hP)
      (fun h => h)) hx

/-- The actual integral closure on the lower inverse-coordinate chart. -/
abbrev infinityTranslationBaseRing :=
  coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityTranslationBaseField

@[instance_reducible] def infinityTranslationBaseRing_baseAlgebra :
    Algebra S.infinityPolynomialBase S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing.algebra

@[instance_reducible] def infinityTranslationBaseRing_baseSMul :
    SMul S.infinityPolynomialBase S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_baseAlgebra.toSMul

@[instance_reducible] def infinityTranslationBaseRing_baseModule :
    Module S.infinityPolynomialBase S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_baseAlgebra.toModule

@[instance_reducible] def infinityTranslationBaseRing_coefficientAlgebra :
    Algebra ↥S.prime.torsionField S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing.algebra'

attribute [local instance] infinityTranslationBaseRing_baseAlgebra
  infinityTranslationBaseRing_baseSMul infinityTranslationBaseRing_baseModule
  infinityTranslationBaseRing_coefficientAlgebra

instance infinityTranslationBaseRing_isDedekindDomain :
    IsDedekindDomain S.infinityTranslationBaseRing :=
  dedekindRing (Genuine.xG S.prime.EK)⁻¹
    S.infinityTranslation_inverseCoordinate_transcendental _

instance infinityTranslationBaseRing_finite :
    Module.Finite S.infinityPolynomialBase S.infinityTranslationBaseRing :=
  finiteRing (Genuine.xG S.prime.EK)⁻¹
    S.infinityTranslation_inverseCoordinate_transcendental _

instance infinityTranslationBaseRing_fractionField :
    IsFractionRing S.infinityTranslationBaseRing S.infinityTranslationBaseField :=
  fractionFieldRing (Genuine.xG S.prime.EK)⁻¹ _

/-- The actual lower-to-upper inclusion on the infinity normalization rings. -/
def infinityTranslationRingMap :
    S.infinityTranslationBaseRing →ₐ[↥S.prime.torsionField] S.infinityNormalizationRing false :=
  ringMap S.infinityTranslationBaseField_le

theorem infinityTranslationRingMap_injective : Function.Injective S.infinityTranslationRingMap :=
  ringMap_injective _

theorem infinityTranslationRingMap_isIntegral : S.infinityTranslationRingMap.toRingHom.IsIntegral :=
  ringMap_isIntegral _

/-- The actual full-TK lower boundary fiber over inverse-coordinate zero. -/
abbrev infinityTranslationBaseFiber :=
  zeroFiber (Genuine.xG S.prime.EK)⁻¹ S.infinityTranslation_inverseCoordinate_transcendental
    S.infinityTranslationBaseField

/-- Contract the existing upper infinity primes along the actual normalization inclusion. -/
def infinityTranslationFiberMap : S.infinityFiber false → S.infinityTranslationBaseFiber :=
  zeroFiberMap S.infinityTranslation_inverseCoordinate_transcendental
    S.infinityTranslationBaseField_le

theorem infinityTranslationFiberMap_asIdeal (q : S.infinityFiber false) :
    (S.infinityTranslationFiberMap q).1 = q.1.comap S.infinityTranslationRingMap.toRingHom := rfl

theorem infinityTranslationFiberMap_surjective : Function.Surjective S.infinityTranslationFiberMap :=
  zeroFiberMap_surjective S.infinityTranslation_inverseCoordinate_transcendental
    S.infinityTranslationBaseField_le

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
