import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogCalibration
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedIntegralLog

/-!
source-id: JT-SCENE1-ACTUAL-LOG-CALIBRATION
source: actual original integral Kummer class, its nonzero log witness and
the ordinary small-ball exponential formula; Joshi III 3190--3236.
fidelity: any linear log satisfying the ordinary small-ball calibration
takes the original actual class to pStar times the paper witness. It
cannot take that same class to the unscaled witness. The explicitly
normalized rational log does give the witness, but fails that calibration.
boundary: Scene1/Derived; no BK map or actual period identity is presumed.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance calibrationPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance calibrationCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance calibrationAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance calibrationContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

set_option maxHeartbeats 1000000 in
theorem originalIntegralImageClass_ordinaryLog
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (actualIntegralImageClass D s).1 =
      (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) * PaperLogWitnessHull.value D s := by
  exact (LocalPadicLog.saturatedPadicLog_principalSaturatedClass
    (k := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (Additive.ofMul (actualPrincipalUnit D s))).trans (log_principalUnit_eq_scale_value D s)

set_option maxHeartbeats 1000000 in
theorem originalIntegralImageClass_normalizedRationalLog
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (actualIntegralImageClass D s).1 =
        PaperLogWitnessHull.value D s := by
  rw [LocalPadicLog.normalizedRationalLog_apply (k := localField D s) (Ω := closure D s)
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1),
    originalIntegralImageClass_ordinaryLog D s,
    inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr
      (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1)))]

set_option maxHeartbeats 1000000 in
theorem calibratedLog_originalIntegralImageClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (L : LocalPadicLog.saturatedKummerPadicSubmodule (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) →ₗ[ℚ_[Arithmetic.residueChar s.1]]
        localField D s)
    (hL : ∀ (z : localField D s) (hz : ‖z‖ ≤ ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖),
      L (LocalPadicLog.principalSaturatedClass (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (Additive.ofMul (LocalPadicLog.smallLogUnit (Arithmetic.residueChar s.1)
          (InitialThetaLogWitness.norm_residueChar_lt_one s.1) z hz))) = z) :
    L (actualIntegralImageClass D s).1 =
      (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) * PaperLogWitnessHull.value D s := by
  rw [LocalPadicLog.linearLog_eq_of_smallLog_calibration (k := localField D s) (Ω := closure D s)
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) L hL]
  exact originalIntegralImageClass_ordinaryLog D s

set_option maxHeartbeats 1000000 in
theorem ordinaryLog_originalIntegralImageClass_ne_witness
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (actualIntegralImageClass D s).1 ≠
        PaperLogWitnessHull.value D s := by
  rw [originalIntegralImageClass_ordinaryLog D s]
  intro h
  have hc : (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) = 1 :=
    mul_right_cancel₀ (PaperLogWitnessHull.value_ne_zero D s) (h.trans (one_mul _).symm)
  have hn := (LocalPadicLog.norm_paperScale_eq_norm_two_mul (Arithmetic.residueChar_prime s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)).trans_lt
    (LocalPadicLog.norm_two_mul_lt_one (InitialThetaLogWitness.norm_residueChar_lt_one s.1))
  rw [hc, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
