import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedIntegralLog
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogCalibration
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotLogShellSource

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-PILOT-INTEGRAL-CLASSES
source: Joshi III 3190--3236 and `eq:bloch-kato-log-class`, with the actual
finite-power integral classes and torsion pilot log-shell norm laws.
fidelity: constructs the original integral Kummer images of
`1 + pStar * qroot^(j^2)` and evaluates their normalized ordinary logarithms
as the canonical torsion pilot values. The contracting q-root norm separates
all natural indices, hence also the finite pilot indices. No divided-class
integral lift or q-order threshold is used.
boundary: Scene1/Derived; original proof. These are actual integral Kummer
images with log/pStar, without an H¹ₑ or Bloch--Kato identification.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionPilotIntegralClasses

open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance sourceCharZero : CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance sourceAlgebra : Algebra ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance sourceFinite : FiniteDimensional ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  LocalCompletion.finite_padicAlgebra (w := s.1) rfl
local instance sourceContinuousSMul : ContinuousSMul ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

abbrev IntegralCarrier :=
  LocalPadicLog.integralKummerSubmodule (Ω := PrincipalUnitKummer.closure D s)
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)

def integralClass (j : ℕ) : IntegralCarrier D s :=
  PrincipalUnitKummer.finitePowerIntegralImageClass D s (j ^ 2)

def logValue (x : IntegralCarrier D s) : PrincipalUnitKummer.localField D s :=
  LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) x.1

theorem integralClass_ordinaryLog (j : ℕ) :
    LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (integralClass D s j).1 =
      LocalPadicLog.padicLog
        ((PrincipalUnitKummer.finitePowerUnit D s (j ^ 2)).1 : PrincipalUnitKummer.localField D s) :=
  LocalPadicLog.saturatedPadicLog_principalSaturatedClass
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (Additive.ofMul (PrincipalUnitKummer.finitePowerUnit D s (j ^ 2)))

theorem integralClass_logValue (j : ℕ) :
    logValue D s (integralClass D s j) =
      InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s j := by
  have hroot : IutInitialThetaQRootFamily.qrootAt D s.1 =
      (iutInitialThetaOddSupportTorsionQRootSource D).qroot s := by
    simp [IutInitialThetaQRootFamily.qrootAt, s.2]
  rw [logValue, LocalPadicLog.normalizedRationalLog_apply, integralClass_ordinaryLog]
  simp only [InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog,
    InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt, hroot]
  rfl

theorem integralClass_logValue_norm (j : ℕ) :
    ‖logValue D s (integralClass D s j)‖ =
      ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ ^ (j ^ 2) := by
  rw [integralClass_logValue]
  exact InitialThetaCanonicalTorsionPilotLogShellSource.canonical_norm_eq_qroot D s j

set_option maxHeartbeats 1000000 in
theorem logValue_zero : logValue D s 0 = 0 :=
  (congrArg (LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1))
    Submodule.coe_zero).trans
    (LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)).map_zero

theorem integralClass_ne_zero (j : ℕ) : integralClass D s j ≠ 0 := by
  intro h
  have hz : logValue D s (integralClass D s j) = 0 := by
    exact (congrArg (logValue D s) h).trans (logValue_zero D s)
  rw [integralClass_logValue] at hz
  exact InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_ne_zero D s j hz

theorem integralClass_injective : Function.Injective (integralClass D s) := by
  intro i j hij
  have hn := congrArg (fun x => ‖logValue D s x‖) hij
  rw [integralClass_logValue_norm, integralClass_logValue_norm] at hn
  have hpos : 0 < ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ :=
    norm_pos_iff.mpr (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1)
  have hlt : ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ < 1 :=
    IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
    (pow_right_injective₀ hpos hlt.ne hn)

/-- The actual finite pilot range inherits separation from its integral classes. -/
def finitePilot (j : Fin (D.prime.ℓ + 1)) : IntegralCarrier D s :=
  integralClass D s j.val

theorem finitePilot_injective : Function.Injective (finitePilot D s) := by
  intro i j hij
  exact Fin.ext (integralClass_injective D s hij)

theorem finitePilot_logValue (j : Fin (D.prime.ℓ + 1)) :
    logValue D s (finitePilot D s j) =
      InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s j.val :=
  integralClass_logValue D s j.val

theorem finitePilot_logValue_norm (j : Fin (D.prime.ℓ + 1)) :
    ‖logValue D s (finitePilot D s j)‖ =
      ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ ^ (j.val ^ 2) :=
  integralClass_logValue_norm D s j.val

theorem finitePilot_logValue_ne_zero (j : Fin (D.prime.ℓ + 1)) :
    logValue D s (finitePilot D s j) ≠ 0 := by
  rw [finitePilot_logValue D s j]
  exact InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_ne_zero D s j.val

theorem finitePilot_logValue_injective :
    Function.Injective (fun j : Fin (D.prime.ℓ + 1) =>
      logValue D s (finitePilot D s j)) := by
  intro i j hij
  have hn := congrArg (fun x => ‖x‖) hij
  rw [finitePilot_logValue_norm D s i, finitePilot_logValue_norm D s j] at hn
  have hpos : 0 < ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ :=
    norm_pos_iff.mpr (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1)
  have hlt : ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ < 1 :=
    IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2
  apply Fin.ext
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
    (pow_right_injective₀ hpos hlt.ne hn)

end
end JoshiTeich.Act1Scene1.InitialThetaTorsionPilotIntegralClasses
