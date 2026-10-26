import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaPadicCompatibility
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittScalarCalibration

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-UNTILT-SCALAR-NORM
source: Joshi II `se:ff-rings` and the canonical untilt evaluation in
the period sequence in the proof of `pr:teichmuller-lift-A`.
fidelity: contraction of actual theta bounds the original untilt scalar
norm by its original fixed-radius scalar norm. Applying the same bound
to the inverse scalar proves equality. The existing positive calibration
therefore gives the standard Q_p scalar norm and exact homogeneity on
the original untilt, without assuming an isometric embedding.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the original untilt field norm is retained.
No new scalar-norm or comparison law is input. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittUntiltScalarNorm

open JoshiTeich.Prologue InitialThetaWittThetaBound
open InitialThetaWittThetaPadicCompatibility InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittPadicScalarNorm InitialThetaWittScalarCalibration
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem norm_untiltPadicMap_le (a : Padic (Arithmetic.residueChar w.1)) :
    ‖untiltPadicMap D w a‖ ≤ ‖completedPadicMap D w (radius D w) a‖ := by
  have h := InitialThetaWittThetaEvaluation.evaluation_norm_le D w (commonPadicMap D w a)
  rw [evaluation_commonPadicMap] at h
  change ‖untiltPadicMap D w a‖ ≤
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w (radius D w) (commonPadicMap D w a)‖ at h
  rwa [evaluate_padic] at h

theorem norm_untiltPadicMap (a : Padic (Arithmetic.residueChar w.1)) :
    ‖untiltPadicMap D w a‖ = ‖completedPadicMap D w (radius D w) a‖ := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, norm_zero]
  apply le_antisymm (norm_untiltPadicMap_le D w a)
  have hc : ‖untiltPadicMap D w a‖ * ‖untiltPadicMap D w a⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, norm_one]
  have hb : ‖completedPadicMap D w (radius D w) a‖ *
      ‖completedPadicMap D w (radius D w) a⁻¹‖ = 1 := by
    rw [← norm_completedPadicMap_mul_scalar, mul_inv_cancel₀ ha, map_one, norm_one]
  calc
    ‖completedPadicMap D w (radius D w) a‖ =
        ‖completedPadicMap D w (radius D w) a‖ *
          (‖untiltPadicMap D w a‖ * ‖untiltPadicMap D w a⁻¹‖) := by rw [hc, mul_one]
    _ = ‖untiltPadicMap D w a‖ *
        (‖completedPadicMap D w (radius D w) a‖ * ‖untiltPadicMap D w a⁻¹‖) := by ring
    _ ≤ ‖untiltPadicMap D w a‖ * (‖completedPadicMap D w (radius D w) a‖ *
        ‖completedPadicMap D w (radius D w) a⁻¹‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_untiltPadicMap_le D w a⁻¹) (norm_nonneg _)) (norm_nonneg _)
    _ = ‖untiltPadicMap D w a‖ := by rw [hb, mul_one]

theorem norm_untiltPadicMap_calibrated (a : Padic (Arithmetic.residueChar w.1)) :
    ‖untiltPadicMap D w a‖ ^ exponent D w (radius D w) = ‖a‖ := by
  rw [norm_untiltPadicMap]
  exact completedPadicMap_rpow D w (radius D w) a

theorem norm_smul_calibrated (a : Padic (Arithmetic.residueChar w.1)) (x : Untilt D w) :
    ‖a • x‖ ^ exponent D w (radius D w) = ‖a‖ * ‖x‖ ^ exponent D w (radius D w) := by
  change ‖untiltPadicMap D w a * x‖ ^ exponent D w (radius D w) = _
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), norm_untiltPadicMap_calibrated]

end
end JoshiTeich.Act1Scene1.InitialThetaWittUntiltScalarNorm
