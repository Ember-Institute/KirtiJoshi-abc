import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidBridgeModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.TateModels
import ArithmeticTeichmullerSpaces.Prologue.Interfaces.Input

namespace JoshiTeich.Prologue.Audit

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Theta
open scoped NumberField

local instance input_padicTwo_not_unit : Fact (¬ IsUnit (2 : ℤ_[2])) :=
  padicTwo_not_unit
local instance input_padicTwo_is_adic_complete :
    IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
  padicTwo_is_adic_complete

noncomputable def padicTwoInputBridgeData :
    @PerfectoidBridgeData ℚ inferInstance inferInstance
      (auditData 2 0 0 0 2 3) ℤ_[2] inferInstance 2 inferInstance
      input_padicTwo_not_unit input_padicTwo_is_adic_complete padicTwoPlaceData :=
  @PerfectoidBridgeData.mk ℚ inferInstance inferInstance
    (auditData 2 0 0 0 2 3) ℤ_[2] inferInstance 2 inferInstance
    input_padicTwo_not_unit input_padicTwo_is_adic_complete padicTwoPlaceData
    padicTwoIntegralMap

noncomputable def padicTwoInputData :
    @PrologueInputData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete :=
  @PrologueInputData.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
    (auditData 2 0 0 0 2 3) padicTwoPlaceData padicTwoInputBridgeData

theorem padicTwo_input_link_model :
    AdelicThetaLink (auditData 2 0 0 0 2 3) := by
  constructor
  · intro w hw j
    change w (2 : ℚ) ^ (j * j) = w ((2 : ℚ) ^ (j * j))
    exact (map_pow w (2 : ℚ) (j * j)).symm
  · exact auditTheta_scaling_laws 0 0
  · intro i
    simp [auditData, auditTheta]
  · change (0 : ℝ) = ∑ _ : Fin 1, (0 : ℝ)
    norm_num

theorem padicTwo_input_bridge_model :
    @PerfectoidBridgeLaws ℚ inferInstance inferInstance
      (auditData 2 0 0 0 2 3) ℤ_[2] inferInstance 2 inferInstance
      input_padicTwo_not_unit input_padicTwo_is_adic_complete padicTwoPlaceData
      padicTwoInputBridgeData := by
  have hlocal :
      @PerfectoidPlaceLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
        inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
        padicTwoPlaceData := by
    exact @PerfectoidPlaceLaws.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance
      2 inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
      padicTwoPlaceData (by
        simpa [padicTwoPlaceData] using padicTwo_perfectoid_model)
  exact @PerfectoidBridgeLaws.mk ℚ inferInstance inferInstance
    (auditData 2 0 0 0 2 3) ℤ_[2] inferInstance 2 inferInstance
    input_padicTwo_not_unit input_padicTwo_is_adic_complete padicTwoPlaceData
    padicTwoInputBridgeData (by
      simp [padicTwoPlaceData, auditData]) hlocal

theorem padicTwo_input_laws :
    @PrologueInputLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
      padicTwoInputData := by
  have hfirst : FirstAxiom (auditData 2 0 0 0 2 3) := by
    constructor
    · simp [auditData]
    · norm_num [auditData]
    · intro w hw
      change 0 < w (2 : ℚ)
      exact NumberField.FinitePlace.pos_iff.mpr (by norm_num)
    · intro x
      change 0 ≤ auditHeight.value x
      exact auditHeight_nonneg x
    · intro i
      change 0 < (1 : ℝ)
      norm_num
    · intro p
      change 0 < (2 : ℝ)
      norm_num
    · intro h
      change 0 < (3 : ℝ)
      norm_num
  exact @PrologueInputLaws.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
    padicTwoInputData
    (by simpa [padicTwoInputData] using hfirst)
    (by change TateParameterLaws auditTateData; exact auditTateData_laws)
    (by exact padicTwo_input_link_model)
    (by exact padicTwo_input_bridge_model)

noncomputable def badInputBridgeData :
    @PerfectoidBridgeData ℚ inferInstance inferInstance
      (auditData 0 0 0 0 2 3) ℤ_[2] inferInstance 2 inferInstance
      input_padicTwo_not_unit input_padicTwo_is_adic_complete padicTwoPlaceData :=
  @PerfectoidBridgeData.mk ℚ inferInstance inferInstance
    (auditData 0 0 0 0 2 3) ℤ_[2] inferInstance 2 inferInstance
    input_padicTwo_not_unit input_padicTwo_is_adic_complete padicTwoPlaceData
    padicTwoIntegralMap

noncomputable def badInputData :
    @PrologueInputData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete :=
  @PrologueInputData.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
    (auditData 0 0 0 0 2 3) padicTwoPlaceData badInputBridgeData

theorem badInput_violates_laws :
    ¬ @PrologueInputLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance input_padicTwo_not_unit input_padicTwo_is_adic_complete
      badInputData := by
  intro h
  have hfirst := @PrologueInputLaws.first_axiom ℚ inferInstance inferInstance
    ℤ_[2] inferInstance 2 inferInstance input_padicTwo_not_unit
    input_padicTwo_is_adic_complete badInputData h
  exact hfirst.q_parameter_nonzero rfl

end JoshiTeich.Prologue.Audit
