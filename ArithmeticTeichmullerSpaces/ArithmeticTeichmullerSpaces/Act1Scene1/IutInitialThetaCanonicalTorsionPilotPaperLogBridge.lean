/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotLogShellSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogShellBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-PILOT-PAPER-LOG-BRIDGE
source: the canonical torsion q-root normalized-log source and the
paper-normalized witness source in `IutInitialThetaPaperLogWitnessHull.lean`.
fidelity: identifies the `j = 1` canonical torsion normalized log with the
same actual paper-normalized witness used by the local log-shell bridge. It
also exports the already proved shell, nonzero, and norm laws on that common
carrier.
boundary: Scene1/Derived; this is a local actual identity. It does not
identify the witness with H¹ₑ, a Bloch--Kato logarithm, a Frechet period, or
the paper theta locus.
-/

namespace InitialThetaCanonicalTorsionPilotPaperLogBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

structure Data (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : Type (u + 1) where
  normalizedLog_one_eq_value :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 =
      PaperLogWitnessHull.value D s
  normalizedLog_one_mem_logShell :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 ∈
      LocalPadicLog.logShell (Arithmetic.residueChar s.1)
  normalizedLog_one_ne_zero :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 ≠ 0
  normalizedLog_one_norm_eq_qroot :
    ‖InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1‖ =
      ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖

noncomputable def canonical : Data D s where
  normalizedLog_one_eq_value := by
    have hq : IutInitialThetaQRootFamily.qrootAt D s.1 =
        (iutInitialThetaOddSupportTorsionQRootSource D).qroot s := by
      simp [IutInitialThetaQRootFamily.qrootAt, s.2]
    simp [InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog,
      InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt,
      PaperLogWitnessHull.value, hq]
  normalizedLog_one_mem_logShell :=
    InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_mem_logShell
      D s 1
  normalizedLog_one_ne_zero :=
    InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_ne_zero D s 1
  normalizedLog_one_norm_eq_qroot := by
    simpa using
      InitialThetaCanonicalTorsionPilotLogShellSource.canonical_norm_eq_qroot D s 1

theorem canonical_normalizedLog_one_eq_value :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 =
      PaperLogWitnessHull.value D s :=
  (canonical D s).normalizedLog_one_eq_value

theorem canonical_value_eq_normalizedLog_one :
    PaperLogWitnessHull.value D s =
      InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 :=
  (canonical_normalizedLog_one_eq_value D s).symm

theorem canonical_normalizedLog_one_mem_logShell :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 ∈
      LocalPadicLog.logShell (Arithmetic.residueChar s.1) :=
  (canonical D s).normalizedLog_one_mem_logShell

theorem canonical_normalizedLog_one_ne_zero :
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 ≠ 0 :=
  (canonical D s).normalizedLog_one_ne_zero

theorem canonical_normalizedLog_one_norm_eq_qroot :
    ‖InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1‖ =
      ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ :=
  (canonical D s).normalizedLog_one_norm_eq_qroot

theorem paperValue_mem_logShell :
    PaperLogWitnessHull.value D s ∈
      LocalPadicLog.logShell (Arithmetic.residueChar s.1) := by
  rw [← canonical_normalizedLog_one_eq_value D s]
  exact canonical_normalizedLog_one_mem_logShell D s

theorem paperValue_ne_zero : PaperLogWitnessHull.value D s ≠ 0 := by
  rw [← canonical_normalizedLog_one_eq_value D s]
  exact canonical_normalizedLog_one_ne_zero D s

theorem paperValue_norm_eq_qroot :
    ‖PaperLogWitnessHull.value D s‖ =
      ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ := by
  rw [← canonical_normalizedLog_one_eq_value D s]
  exact canonical_normalizedLog_one_norm_eq_qroot D s

end InitialThetaCanonicalTorsionPilotPaperLogBridge

end
end JoshiTeich.Act1Scene1
