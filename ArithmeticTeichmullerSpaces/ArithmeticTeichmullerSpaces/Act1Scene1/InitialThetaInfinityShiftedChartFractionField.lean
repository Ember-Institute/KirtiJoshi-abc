import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedFunctionFieldImage
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedAffineChart
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassPointRawChartFractionField

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: JT-SCENE1-GENUINE-DIVISION-POINT-EVALUATION;
JT-SCENE1-GENUINE-DIVISION-POINT-FUNCTION-FIELD-IMAGE
source: the original shifted chart, its original function-field evaluator,
and the canonical raw-chart fraction-field theorem.
fidelity: the ORIGINAL shifted chart has as fraction field the image of
its SAME evaluator in the ORIGINAL normal closure. Mapping that image by
the ORIGINAL ambient inclusion gives the ORIGINAL unsigned full
normalization field, with scalars restricted to the original coefficient field.
boundary: the entire normal closure is not asserted to be this fraction
field. No denominator-unit or upper residue-field identity is proved here.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 2000] Classical.propDecidable
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityDivisionNormalClosure_field infinityDivisionNormalClosure_rationalAlgebra
  infinityDivisionNormalClosure_baseAlgebra infinityDivisionNormalClosure_baseSMul
  infinityDivisionNormalClosure_baseModule infinityDivisionNormalClosure_coefficientAlgebra
  infinityDivisionNormalClosure_coefficientSMul infinityDivisionNormalClosure_coefficientModule
  infinityDivisionNormalClosure_coefficientBaseTower infinityDivisionNormalClosure_baseTower
  shiftedDivisionClosureTranscendence_decidableEq
  shiftedAffineChart_commRing shiftedAffineChart_isDomain
  shiftedAffineChart_coefficientAlgebra shiftedAffineChart_coefficientSMul
  shiftedAffineChart_coefficientModule

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The image of the SAME actual evaluator, inside the ORIGINAL normal closure. -/
abbrev infinityDivisionClosureShiftedChartFractionField :
    IntermediateField ↥S.prime.torsionField S.infinityDivisionNormalClosure :=
  S.infinityDivisionClosureShiftedFunctionFieldAlgHom.fieldRange

local instance shiftedChartFraction_field :
    Field S.infinityDivisionClosureShiftedChartFractionField :=
  S.infinityDivisionClosureShiftedChartFractionField.toSubfield.toField

local instance shiftedChartFraction_coefficientAlgebra :
    Algebra ↥S.prime.torsionField S.infinityDivisionClosureShiftedChartFractionField :=
  IntermediateField.algebra' _

local instance shiftedChartFraction_coefficientSMul :
    SMul ↥S.prime.torsionField S.infinityDivisionClosureShiftedChartFractionField :=
  S.shiftedChartFraction_coefficientAlgebra.toSMul

local instance shiftedChartFraction_coefficientModule :
    Module ↥S.prime.torsionField S.infinityDivisionClosureShiftedChartFractionField :=
  S.shiftedChartFraction_coefficientAlgebra.toModule

/-- The canonical inclusion of the ORIGINAL chart into its evaluator image. -/
@[instance_reducible] def infinityDivisionClosureShiftedChartFractionAlgebra :
    Algebra S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField :=
  WeierstrassPointRawChartFractionField.rawChartFieldRangeAlgebra S.prime.EK
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental

attribute [local instance] infinityDivisionClosureShiftedChartFractionAlgebra

local instance shiftedChartFraction_chartSMul :
    SMul S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField :=
  S.infinityDivisionClosureShiftedChartFractionAlgebra.toSMul

local instance shiftedChartFraction_chartModule :
    Module S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField :=
  S.infinityDivisionClosureShiftedChartFractionAlgebra.toModule

local instance shiftedChartFraction_chartAmbientAlgebra :
    Algebra S.infinityDivisionClosureShiftedAffineChart S.infinityDivisionNormalClosure :=
  S.infinityDivisionClosureShiftedAffineChart.toAlgebra

local instance shiftedChartFraction_chartAmbientSMul :
    SMul S.infinityDivisionClosureShiftedAffineChart S.infinityDivisionNormalClosure :=
  S.shiftedChartFraction_chartAmbientAlgebra.toSMul

local instance shiftedChartFraction_chartAmbientModule :
    Module S.infinityDivisionClosureShiftedAffineChart S.infinityDivisionNormalClosure :=
  S.shiftedChartFraction_chartAmbientAlgebra.toModule

local instance shiftedChartFraction_imageAmbientAlgebra :
    Algebra S.infinityDivisionClosureShiftedChartFractionField
      S.infinityDivisionNormalClosure :=
  S.infinityDivisionClosureShiftedChartFractionField.toAlgebra

local instance shiftedChartFraction_imageAmbientSMul :
    SMul S.infinityDivisionClosureShiftedChartFractionField S.infinityDivisionNormalClosure :=
  S.shiftedChartFraction_imageAmbientAlgebra.toSMul

local instance shiftedChartFraction_imageAmbientModule :
    Module S.infinityDivisionClosureShiftedChartFractionField S.infinityDivisionNormalClosure :=
  S.shiftedChartFraction_imageAmbientAlgebra.toModule

/-- The coefficient map commutes with the SAME chart-to-image inclusion. -/
theorem infinityDivisionClosureShiftedChartFractionField_coefficientTower :
    IsScalarTower ↥S.prime.torsionField S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField :=
  WeierstrassPointRawChartFractionField.coefficientTower S.prime.EK
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental

/-- The original inclusions of the chart and its image agree in the normal closure. -/
theorem infinityDivisionClosureShiftedChartFractionField_ambientTower :
    IsScalarTower S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField S.infinityDivisionNormalClosure :=
  WeierstrassPointRawChartFractionField.ambientTower S.prime.EK
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental

/-- The SAME evaluator image is a fraction field of the ORIGINAL shifted affine chart. -/
theorem infinityDivisionClosureShiftedAffineChart_isFractionRing :
    IsFractionRing S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField :=
  WeierstrassPointRawChartFractionField.isFractionRing_fieldRange S.prime.EK
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental

/-- The canonical fraction-field inclusion retains the ORIGINAL normal-closure value. -/
@[simp] theorem infinityDivisionClosureShiftedChartFractionField_coe_algebraMap
    (a : S.infinityDivisionClosureShiftedAffineChart) :
    (algebraMap S.infinityDivisionClosureShiftedAffineChart
      S.infinityDivisionClosureShiftedChartFractionField a : S.infinityDivisionNormalClosure) =
        (a : S.infinityDivisionNormalClosure) :=
  WeierstrassPointRawChartFractionField.coe_algebraMap S.prime.EK
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental a

/-- After the ORIGINAL inclusion into Ω, the SAME original ambient value is retained. -/
@[simp] theorem infinityDivisionClosureShiftedChartFractionField_ambient_algebraMap
    (a : S.infinityDivisionClosureShiftedAffineChart) :
    S.infinityDivisionClosureShiftedAmbientInclusion
      (algebraMap S.infinityDivisionClosureShiftedAffineChart
        S.infinityDivisionClosureShiftedChartFractionField a : S.infinityDivisionNormalClosure) =
      S.infinityDivisionClosureShiftedAmbientInclusion (a : S.infinityDivisionNormalClosure) :=
  congrArg S.infinityDivisionClosureShiftedAmbientInclusion
    (S.infinityDivisionClosureShiftedChartFractionField_coe_algebraMap a)

/-- This chart's actual fraction-field image maps to the ORIGINAL full normalization field. -/
theorem infinityDivisionClosureShiftedChartFractionField_map_normalization :
    S.infinityDivisionClosureShiftedChartFractionField.map
      S.infinityDivisionClosureShiftedAmbientInclusion =
        (Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false).restrictScalars
          ↥S.prime.torsionField :=
  S.infinityDivisionClosureShiftedFunctionFieldAlgHom_fieldRange_map_normalization

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
