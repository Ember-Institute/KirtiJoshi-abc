import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedDivisionTranscendence
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineShiftedDivisionFunctionFieldImage
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassPointEvaluationNaturality
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: JT-SCENE1-GENUINE-DIVISION-POINT-EVALUATION;
JT-SCENE1-GENUINE-DIVISION-POINT-FUNCTION-FIELD-IMAGE
fidelity: evaluates at the ORIGINAL shifted point in the ORIGINAL normal
closure, then compares its original ambient inclusion with an evaluator at
the SAME ambient shifted point. Both image fields are compared over the
original coefficient field k, explicitly restricting the original QField
from its baseField scalar structure. No replacement point or field is chosen.
boundary: this module identifies the mapped function-field image; chart
fraction-field and localization conclusions are separate consumers.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve Polynomial
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

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- Evaluate the original elliptic function field at the SAME original shifted Qpt in N. -/
def infinityDivisionClosureShiftedFunctionFieldAlgHom :
    S.prime.EK.toAffine.FunctionField →ₐ[↥S.prime.torsionField]
      S.infinityDivisionNormalClosure :=
  WeierstrassTranscendentalPointEvaluation.functionFieldAlgHom S.prime.EK
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental

/-- The ORIGINAL inclusion of the original normal closure in the original ambient closure. -/
def infinityDivisionClosureShiftedAmbientInclusion :
    S.infinityDivisionNormalClosure →ₐ[↥S.prime.torsionField]
      Genuine.Ω S.prime.EK :=
  S.infinityDivisionNormalClosure.val.restrictScalars ↥S.prime.torsionField

/-- The original finite-closure evaluation becomes the named SAME shifted ambient evaluation. -/
theorem infinityDivisionClosureShiftedFunctionFieldAlgHom_comp_ambient :
    (S.infinityDivisionClosureShiftedAmbientInclusion).comp
      S.infinityDivisionClosureShiftedFunctionFieldAlgHom =
        Genuine.shiftedDivisionPointFunctionFieldAlgHom S.prime.EK S.prime.ℓ
          S.prime.ℓ_prime.pos S.infinityTwoTorsionShift := by
  let Q : (S.prime.EK⁄(Genuine.Ω S.prime.EK)).toAffine.Point :=
    Affine.Point.add (W := (S.prime.EK⁄(Genuine.Ω S.prime.EK)).toAffine)
      (Genuine.Qpt S.prime.EK S.prime.ℓ)
      (Genuine.base S.prime.EK S.infinityTwoTorsionShift)
  have hxQ : Transcendental ↥S.prime.torsionField (ptX Q) :=
    Genuine.Qpt_add_base_x_transcendental S.prime.EK S.prime.ℓ
      S.prime.ℓ_prime.pos S.infinityTwoTorsionShift
  have hQ : Q ≠ 0 := by
    intro h
    exact hxQ.ne_zero (by rw [h]; rfl)
  exact (WeierstrassPointEvaluationNaturality.functionFieldAlgHom_comp
    S.prime.EK S.infinityDivisionClosureShiftedAmbientInclusion
    S.infinityDivisionClosureShiftedQpt S.infinityDivisionClosureShiftedQpt_ne_zero
    S.infinityDivisionClosureShiftedQpt_x_transcendental Q hQ hxQ
    S.infinityDivisionClosureShiftedQpt_map).trans
    (Genuine.shiftedDivisionPointFunctionFieldAlgHom_eq_functionFieldAlgHom
      S.prime.EK S.prime.ℓ S.prime.ℓ_prime.pos S.infinityTwoTorsionShift hQ hxQ).symm

/-- The finite-closure evaluator's ambient image is the ORIGINAL full division-coordinate field. -/
theorem infinityDivisionClosureShiftedFunctionFieldAlgHom_fieldRange_map :
    S.infinityDivisionClosureShiftedFunctionFieldAlgHom.fieldRange.map
      S.infinityDivisionClosureShiftedAmbientInclusion =
        (Genuine.QField S.prime.EK S.prime.ℓ).restrictScalars ↥S.prime.torsionField := by
  exact (AlgHom.map_fieldRange S.infinityDivisionClosureShiftedFunctionFieldAlgHom
    S.infinityDivisionClosureShiftedAmbientInclusion).trans
    ((congrArg AlgHom.fieldRange
      S.infinityDivisionClosureShiftedFunctionFieldAlgHom_comp_ambient).trans
      (Genuine.shiftedDivisionPointFunctionFieldAlgHom_fieldRange
        S.prime.EK S.prime.ℓ S.prime.ℓ_prime.pos S.infinityTwoTorsionShift))

/-- The SAME mapped image is the original unsigned full normalization field over k. -/
theorem infinityDivisionClosureShiftedFunctionFieldAlgHom_fieldRange_map_normalization :
    S.infinityDivisionClosureShiftedFunctionFieldAlgHom.fieldRange.map
      S.infinityDivisionClosureShiftedAmbientInclusion =
        (Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false).restrictScalars
          ↥S.prime.torsionField := by
  rw [S.infinityDivisionClosureShiftedFunctionFieldAlgHom_fieldRange_map]
  ext z
  change z ∈ Genuine.QField S.prime.EK S.prime.ℓ ↔
    z ∈ Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false
  rw [Genuine.mem_normalizationField, Genuine.stabilizerField_bot_false_eq_QField]

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
