import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionThetaPilotReferenceBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open InitialThetaCanonicalGeometricFontaine

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-THETA-PILOT-NORMALIZATION
source: the finite torsion theta pilot and its local Tate-log period bridge.
fidelity: sums the proved local `j²/(2ℓ)` period formula over the actual
finite pilot index. This is an actual finite normalization identity.
boundary: it does not identify the sum with a paper Frechet log-volume or
global thetaVolume.
-/

namespace InitialThetaCanonicalTorsionThetaPilotSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)

theorem canonical_period_sum_eq_tate_log_mul_square_sum :
    ∑ i : InitialThetaTorsionThetaPilotScaling.PilotIndex D,
      (Pilot D w v hvw).period i =
      (∑ i : InitialThetaTorsionThetaPilotScaling.PilotIndex D,
        ((i.down.val ^ 2 : ℕ) : ℝ)) /
          ((2 * D.prime.ℓ : ℕ) : ℝ) *
        Real.log ((iutInitialThetaTateParameterData D).norm w.1) := by
  calc
    ∑ i : InitialThetaTorsionThetaPilotScaling.PilotIndex D,
        (Pilot D w v hvw).period i =
        ∑ i : InitialThetaTorsionThetaPilotScaling.PilotIndex D,
          (((i.down.val ^ 2 : ℕ) : ℝ) /
            ((2 * D.prime.ℓ : ℕ) : ℝ)) *
            Real.log ((iutInitialThetaTateParameterData D).norm w.1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [canonical_period_eq_tate_log D w v hvw i]
    _ = (∑ i : InitialThetaTorsionThetaPilotScaling.PilotIndex D,
          ((i.down.val ^ 2 : ℕ) : ℝ)) /
          ((2 * D.prime.ℓ : ℕ) : ℝ) *
        Real.log ((iutInitialThetaTateParameterData D).norm w.1) := by
      rw [← Finset.sum_mul]
      rw [Finset.sum_div]

end InitialThetaCanonicalTorsionThetaPilotSource

end
end JoshiTeich.Act1Scene1
