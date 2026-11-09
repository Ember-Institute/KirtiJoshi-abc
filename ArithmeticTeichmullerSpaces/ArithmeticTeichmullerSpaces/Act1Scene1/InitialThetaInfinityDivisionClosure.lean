import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationBaseIdentity
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationFields
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationGalois

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: the existing actual division normal closure is rebased to the same
inverse-coordinate line. The generic and division coordinates retain the same
ambient values. No new field choice or geometry law is supplied by the caller.
-/
namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
open WeierstrassCurve
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
  Genuine.finite_divisionNormalClosure Genuine.galois_divisionNormalClosure
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

def infinityDivisionNormalClosure :
    IntermediateField
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (Genuine.Ω S.prime.EK) :=
  rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.divisionNormalClosure S.prime.EK S.prime.ℓ)

local instance infinityDivisionNormalClosure_field :
    Field S.infinityDivisionNormalClosure :=
  S.infinityDivisionNormalClosure.toSubfield.toField
local instance infinityDivisionNormalClosure_rationalAlgebra :
    Algebra (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure := IntermediateField.algebra' _
local instance infinityDivisionNormalClosure_baseAlgebra :
    Algebra (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure := IntermediateField.algebra' _
local instance infinityDivisionNormalClosure_baseSMul :
    SMul (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure := S.infinityDivisionNormalClosure_baseAlgebra.toSMul
local instance infinityDivisionNormalClosure_baseModule :
    Module (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure := S.infinityDivisionNormalClosure_baseAlgebra.toModule
local instance infinityDivisionNormalClosure_coefficientAlgebra :
    Algebra ↥S.prime.torsionField S.infinityDivisionNormalClosure := IntermediateField.algebra' _
local instance infinityDivisionNormalClosure_coefficientSMul :
    SMul ↥S.prime.torsionField S.infinityDivisionNormalClosure :=
  S.infinityDivisionNormalClosure_coefficientAlgebra.toSMul
local instance infinityDivisionNormalClosure_coefficientModule :
    Module ↥S.prime.torsionField S.infinityDivisionNormalClosure :=
  S.infinityDivisionNormalClosure_coefficientAlgebra.toModule
local instance infinityDivisionNormalClosure_coefficientBaseTower :
    IsScalarTower ↥S.prime.torsionField
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance infinityDivisionNormalClosure_baseTower :
    IsScalarTower (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance finiteDimensional_infinityDivisionNormalClosure :
    FiniteDimensional
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure :=
  finiteDimensional_rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine _

private lemma isGalois_rebaseField {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    {B B' : IntermediateField k Ω} (h : B = B') (D : IntermediateField B Ω)
    [IsGalois B D] : IsGalois B' (rebaseField h D) := by
  subst B'
  change IsGalois B D
  infer_instance

instance isGalois_infinityDivisionNormalClosure :
    IsGalois (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure :=
  isGalois_rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine _

theorem infinityDivisionNormalClosure_contains_fullDivision
    {a : Genuine.Ω S.prime.EK}
    (ha : a ∈ Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false) :
    a ∈ S.infinityDivisionNormalClosure :=
  (mem_rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.divisionNormalClosure S.prime.EK S.prime.ℓ) a).mpr
    (Genuine.normalizationFull_le_divisionNormalClosure S.prime.EK S.prime.ℓ ha)

theorem infinityDivisionNormalClosure_xG_mem :
    Genuine.xG S.prime.EK ∈ S.infinityDivisionNormalClosure :=
  (mem_rebaseField S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.divisionNormalClosure S.prime.EK S.prime.ℓ) _).mpr
    ((Genuine.divisionNormalClosure S.prime.EK S.prime.ℓ).algebraMap_mem
      ⟨Genuine.xG S.prime.EK, Genuine.xG_mem_xLine S.prime.EK⟩)

theorem infinityDivisionNormalClosure_yG_mem :
    Genuine.yG S.prime.EK ∈ S.infinityDivisionNormalClosure :=
  S.infinityDivisionNormalClosure_contains_fullDivision
    (Genuine.normalization_yG_mem_unsigned S.prime.EK S.prime.ℓ ⊥)

theorem infinityTranslationBaseField_xG_mem :
    Genuine.xG S.prime.EK ∈ S.infinityTranslationBaseField := by
  rw [S.infinityTranslationBaseField_eq_elliptic]
  change Genuine.xG S.prime.EK ∈ Genuine.normalizationField S.prime.EK 1 ⊥ false
  exact (Genuine.normalizationField S.prime.EK 1 ⊥ false).algebraMap_mem
    ⟨Genuine.xG S.prime.EK, Genuine.xG_mem_xLine S.prime.EK⟩

theorem infinityTranslationBaseField_yG_mem :
    Genuine.yG S.prime.EK ∈ S.infinityTranslationBaseField := by
  rw [S.infinityTranslationBaseField_eq_elliptic]
  exact Genuine.normalization_yG_mem_unsigned S.prime.EK 1 ⊥

theorem infinityDivisionNormalClosure_Qpt_coordinates_mem :
    ptX (Genuine.Qpt S.prime.EK S.prime.ℓ) ∈ S.infinityDivisionNormalClosure ∧
      ptY (Genuine.Qpt S.prime.EK S.prime.ℓ) ∈ S.infinityDivisionNormalClosure :=
  ⟨S.infinityDivisionNormalClosure_contains_fullDivision
      (Genuine.Qpt_coordinates_mem_normalizationField S.prime.EK S.prime.ℓ).1,
    S.infinityDivisionNormalClosure_contains_fullDivision
      (Genuine.Qpt_coordinates_mem_normalizationField S.prime.EK S.prime.ℓ).2⟩

/-- The original lower elliptic field is contained in the same actual closure. -/
theorem infinityTranslationBaseField_le_divisionNormalClosure :
    S.infinityTranslationBaseField ≤ S.infinityDivisionNormalClosure := by
  exact rebaseField_mono S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.normalization_unsigned_le_divisionNormalClosure
      S.prime.EK S.prime.ℓ S.prime.TK)

/-- The original unsigned upper cover is contained in the same actual closure. -/
theorem infinityUnsignedField_le_divisionNormalClosure :
    S.infinityNormalizationField false ≤ S.infinityDivisionNormalClosure := by
  exact rebaseField_mono S.infinityTranslation_xLine_eq_inverseCoordinateLine
    (Genuine.normalization_unsigned_le_divisionNormalClosure
      S.prime.EK S.prime.ℓ S.prime.M)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
