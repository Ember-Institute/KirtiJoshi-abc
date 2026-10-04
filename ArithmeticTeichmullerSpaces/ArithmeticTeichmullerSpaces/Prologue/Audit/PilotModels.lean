import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Theta.Pilot

namespace JoshiTeich.Prologue.Audit

open JoshiTeich.Prologue.Theta

noncomputable def auditScalingTheta : ThetaPilotData ℚ where
  index := Bool
  indexFintype := inferInstance
  value := fun i => if i then 3 else 2
  norm := fun i => if i then (1 / 16 : ℝ) else (1 / 2 : ℝ)
  scalingIndex := fun i => if i then 2 else 1
  frobenius := fun i => i
  period := fun i => if i then 2 else 1
  liftedLog := fun i => if i then 2 else 1

theorem auditScalingTheta_laws :
    ThetaPilotScalingLaws auditScalingTheta false := by
  refine ⟨by change (1 : ℕ) = 1; rfl, ?_, ?_, ?_⟩
  · intro i
    cases i
    · change (2 : ℚ) ≠ 0
      norm_num
    · change (3 : ℚ) ≠ 0
      norm_num
  · intro i
    cases i
    · change 0 < (1 / 2 : ℝ)
      norm_num
    · change 0 < (1 / 16 : ℝ)
      norm_num
  · intro i
    cases i
    · change (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 * 1)
      norm_num
    · change (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ (2 * 2)
      norm_num

noncomputable def zeroScalingTheta : ThetaPilotData ℚ where
  index := Bool
  indexFintype := inferInstance
  value := fun _ => 0
  norm := fun i => if i then (1 / 16 : ℝ) else (1 / 2 : ℝ)
  scalingIndex := fun i => if i then 2 else 1
  frobenius := fun i => i
  period := fun i => if i then 2 else 1
  liftedLog := fun i => if i then 2 else 1

theorem zeroScalingTheta_violates_laws :
    ¬ ThetaPilotScalingLaws zeroScalingTheta false := by
  intro h
  have hv := h.value_nonzero false
  change (0 : ℚ) ≠ 0 at hv
  exact hv rfl

end JoshiTeich.Prologue.Audit
