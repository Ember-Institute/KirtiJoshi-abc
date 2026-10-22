import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogCalibration
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedIntegralLog

/-!
source-id: JT-SCENE1-INITIAL-THETA-BK-NORMALIZATION-AUDIT
source: Joshi III ss:bloch-kato-exp and ss:bloch-kato-logarithm,
eq:bloch-kato-log-class (3210--3236), together with the actual Kummer/log
calibration already proved in Scene1.
fidelity: for the actual principal-unit Kummer class, packages the two
possible normalizations. The ordinary small-ball calibration uniquely forces
unscaled ordinary logarithm and therefore sends the original integral class to
p* times the paper witness. The p*-divided comparison sends that class to the
paper witness but provably fails the same small-ball calibration. This is a
normalization/source audit; it does not identify either map with H^1_e or
construct the Bloch--Kato comparison.
Original proofs; no reference code copied; Prologue-R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer.BlochKatoNormalizationAudit

open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance auditPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance auditCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance auditAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (PrincipalUnitKummer.localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance auditContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (PrincipalUnitKummer.localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

abbrev Carrier (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  LocalPadicLog.saturatedKummerPadicSubmodule (k := PrincipalUnitKummer.localField D s)
    (Ω := PrincipalUnitKummer.closure D s) (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)

abbrev Base (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  PrincipalUnitKummer.localField D s

theorem actualIntegralClass_ordinaryLog
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (PrincipalUnitKummer.actualIntegralImageClass D s).1 =
      (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : Base D s) *
        PaperLogWitnessHull.value D s :=
  PrincipalUnitKummer.originalIntegralImageClass_ordinaryLog D s

theorem actualIntegralClass_normalizedComparison
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
      (PrincipalUnitKummer.actualIntegralImageClass D s).1 =
        PaperLogWitnessHull.value D s :=
  PrincipalUnitKummer.originalIntegralImageClass_normalizedRationalLog D s

set_option maxHeartbeats 1000000 in
theorem ordinaryComparison_unique_of_smallBallCalibration
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (L : Carrier D s →ₗ[ℚ_[Arithmetic.residueChar s.1]] Base D s)
    (hL : ∀ (z : Base D s) (hz : ‖z‖ ≤
      ‖2 * (Arithmetic.residueChar s.1 : Base D s)‖),
      L (LocalPadicLog.principalSaturatedClass (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (Additive.ofMul (LocalPadicLog.smallLogUnit
          (Arithmetic.residueChar s.1)
          (InitialThetaLogWitness.norm_residueChar_lt_one s.1) z hz))) = z) :
    L = LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) := by
  exact LocalPadicLog.linearLog_eq_of_smallLog_calibration
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    L hL

theorem normalizedComparison_not_smallBallCalibrated
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ¬ (∀ (z : Base D s) (hz : ‖z‖ ≤
      ‖2 * (Arithmetic.residueChar s.1 : Base D s)‖),
      LocalPadicLog.normalizedRationalLog (k := Base D s) (Ω := PrincipalUnitKummer.closure D s)
        (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (LocalPadicLog.principalSaturatedClass (k := Base D s)
          (Ω := PrincipalUnitKummer.closure D s) (Arithmetic.residueChar s.1)
          (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
          (Additive.ofMul (LocalPadicLog.smallLogUnit
            (Arithmetic.residueChar s.1)
            (InitialThetaLogWitness.norm_residueChar_lt_one s.1) z hz))) = z) := by
  exact LocalPadicLog.normalizedRationalLog_fails_smallLog_calibration
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer.BlochKatoNormalizationAudit
