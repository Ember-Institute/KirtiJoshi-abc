import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogBallIndex
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOG-BALL-NORM
source: Joshi III `le:volume-lemma1`; actual canonical q-root logarithm
integral ball and local principal quotient counting.
fidelity: proves actual local normalized Haar measure equals raw
completion root norm. It does not identify this ball with a theta locus
in another untilt or with the final tensor/hull volume.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaLogWitness

open JoshiTeich.Prologue NumberField MeasureTheory

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

set_option maxHeartbeats 1000000 in
theorem integralBall_index_eq_absNorm_pow
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    LocalCompletion.principalIndex v.1 (integralValue D v) =
      Ideal.absNorm v.1.maximalIdeal.asIdeal ^ Arithmetic.completionQOrder v.1 (value D v) := by
  exact LocalCompletion.principalIndex_eq_absNorm_pow v.1 (integralValue D v)
    (integralValue_ne_zero D v) _ (Arithmetic.completionQOrder_valued v.1 (value D v)
      (value_ne_zero D v) (by
        rw [norm_value_eq_qroot_norm D v]
        exact IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v))

set_option maxHeartbeats 1000000 in
theorem integralBall_haar_toReal_eq_qroot_norm
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    (LocalCompletion.normalizedHaar v.1 (integralBall D v)).toReal =
      ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ := by
  rw [← norm_value_eq_qroot_norm D v]
  simpa only [integralBall, integralValue] using
    (LocalCompletion.normalizedHaar_scalarBall_toReal_eq_norm v.1 (integralValue D v)
      (integralValue_ne_zero D v) _ (Arithmetic.completionQOrder_valued v.1 (value D v)
        (value_ne_zero D v) (by
          rw [norm_value_eq_qroot_norm D v]
          exact IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v)))

theorem integralBall_haar_eq_qroot_norm
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    LocalCompletion.normalizedHaar v.1 (integralBall D v) =
      ENNReal.ofReal ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ := by
  rw [← integralBall_haar_toReal_eq_qroot_norm D v]
  exact (ENNReal.ofReal_toReal (integralBall_haar_pos_lt_top D v).2.ne).symm

end
end JoshiTeich.Act1Scene1.InitialThetaLogWitness
