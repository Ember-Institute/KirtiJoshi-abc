/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotPaperLogBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedKummerLog

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

set_option maxHeartbeats 1000000

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-PILOT-SATURATED-KUMMER-LOG-BRIDGE
source: the canonical torsion pilot normalized-log source, the
paper-normalized witness bridge, and the actual saturated Kummer logarithm.
fidelity: proves that the same local normalized value at `j = 1` is the
canonical torsion log, the paper-normalized witness, and the saturated-image
log of `normalizedSaturatedClass`. This is a source identity inside one
actual completion.
boundary: Scene1/Derived; it does not identify the saturated carrier with
H¹ₑ, crystalline cohomology, or Bloch--Kato data.
-/

namespace InitialThetaCanonicalTorsionPilotSaturatedKummerLogBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance saturatedLogPrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance saturatedLogCharZero :
    CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem canonical_normalizedLog_one_eq_saturatedImageLog :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 =
      LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (PrincipalUnitKummer.normalizedSaturatedClass D s) :=
  by
    rw [InitialThetaCanonicalTorsionPilotPaperLogBridge.canonical_normalizedLog_one_eq_value D s]
    exact (PrincipalUnitKummer.normalizedSaturatedClass_saturatedImageLog_eq_value D s).symm

theorem canonical_saturatedImageLog_eq_normalizedLog_one :
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (PrincipalUnitKummer.normalizedSaturatedClass D s) =
      InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 :=
  (canonical_normalizedLog_one_eq_saturatedImageLog D s).symm

theorem canonical_saturatedImageLog_eq_paperValue :
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (PrincipalUnitKummer.normalizedSaturatedClass D s) =
      PaperLogWitnessHull.value D s :=
  PrincipalUnitKummer.normalizedSaturatedClass_saturatedImageLog_eq_value D s

theorem canonical_normalizedLog_one_eq_paperValue :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 =
      PaperLogWitnessHull.value D s := by
  rw [canonical_normalizedLog_one_eq_saturatedImageLog D s]
  exact canonical_saturatedImageLog_eq_paperValue D s

theorem canonical_normalizedLog_one_ne_zero :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 ≠ 0 :=
  InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_ne_zero D s 1

theorem canonical_saturatedImageLog_ne_zero :
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (PrincipalUnitKummer.normalizedSaturatedClass D s) ≠ 0 := by
  rw [canonical_saturatedImageLog_eq_normalizedLog_one D s]
  exact canonical_normalizedLog_one_ne_zero D s

end InitialThetaCanonicalTorsionPilotSaturatedKummerLogBridge

end
end JoshiTeich.Act1Scene1
