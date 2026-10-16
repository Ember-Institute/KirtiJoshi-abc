import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralLogLattice
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaKummerLogShell

/-!
source-id: JT-SCENE1-ACTUAL-INTEGRAL-LOG-CRITERION
source: actual normalized rational class and ordinary witness, Joshi III
3226--3236, and the proved original integral-image intersection.
fidelity: integral lifting of the existing normalized class is equivalent
to membership of the original witness in the unscaled ordinary-log image.
The scaled original witness belongs to this image unconditionally. No
H1e/BK identity or normalized-class integral lift is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance integralLogPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance integralLogCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance integralLogAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance integralLogContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

set_option maxHeartbeats 1000000 in
theorem normalizedClass_integralLift_iff_value_mem_principalLogImage
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s) ↔
      PaperLogWitnessHull.value D s ∈ LocalPadicLog.principalLogImage (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) := by
  have h := LocalPadicLog.integralLift_iff_log_mem_principalLogImage
    (k := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (normalizedPadicClass D s)
  have hv : LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (normalizedPadicClass D s) =
        PaperLogWitnessHull.value D s :=
    normalizedSaturatedClass_saturatedImageLog_eq_value D s
  rw [hv] at h
  exact h

theorem scale_value_mem_principalLogImage
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) * PaperLogWitnessHull.value D s ∈
      LocalPadicLog.principalLogImage (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) := by
  rw [← log_principalUnit_eq_scale_value D s]
  exact (LocalPadicLog.mem_principalLogImage_iff _ _ _).mpr
    ⟨PaperLogWitnessHull.principalUnit D s, PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s, rfl⟩

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
