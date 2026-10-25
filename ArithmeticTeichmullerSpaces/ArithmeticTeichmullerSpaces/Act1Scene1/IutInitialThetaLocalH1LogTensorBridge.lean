/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotLocalH1LogBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotTensorLogShellBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

set_option maxHeartbeats 1000000

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-LOCAL-H1-LOG-TENSOR-BRIDGE
source: the local actual H¹/log source-consistency package and the actual
canonical torsion/paper tensor witness package.
fidelity: forms a pure tensor from the normalized logs of the local actual
H¹/log source and proves equality with the canonical torsion tensor witness.
Tensor log-shell membership and unitness therefore hold for the H¹/log
representative itself.
boundary: Scene1/Derived; this is an actual local tensor identity. It does
not identify the tensor with H¹ₑ/BK data, a Frechet period, or the paper theta
locus.
-/

namespace InitialThetaLocalH1LogTensorBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

abbrev packet (v : iutInitialThetaOddModSupportFinset D) :=
  PaperLogWitnessHull.packet D n v

local instance paperTensorPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

noncomputable def h1Witness
    (v : iutInitialThetaOddModSupportFinset D) : (packet D n v).Tensor :=
  (packet D n v).pure (fun i =>
    (InitialThetaLocalH1LogSource.canonical D
      (FullSupportThetaLogHull.sourceAt D n v i)).normalizedLog)

theorem h1Witness_eq_canonicalWitness
    (v : iutInitialThetaOddModSupportFinset D) :
    h1Witness D n v =
      InitialThetaCanonicalTorsionPilotTensorLogShellBridge.canonicalWitness D n v := by
  unfold h1Witness InitialThetaCanonicalTorsionPilotTensorLogShellBridge.canonicalWitness
  apply congrArg (packet D n v).pure
  funext i
  exact
    InitialThetaCanonicalTorsionPilotLocalH1LogBridge.canonical_h1_normalizedLog_eq_torsion_normalizedLog
      D (FullSupportThetaLogHull.sourceAt D n v i)

theorem h1Witness_eq_paperWitness
    (v : iutInitialThetaOddModSupportFinset D) :
    h1Witness D n v = PaperLogWitnessHull.witness D n v := by
  rw [h1Witness_eq_canonicalWitness D n v]
  exact
    InitialThetaCanonicalTorsionPilotTensorLogShellBridge.canonicalWitness_eq_witness D n v

theorem h1Witness_mem_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    h1Witness D n v ∈ (packet D n v).tensorLogShell := by
  rw [h1Witness_eq_canonicalWitness D n v]
  exact
    InitialThetaCanonicalTorsionPilotTensorLogShellBridge.canonicalWitness_mem_tensorLogShell
      D n v

theorem h1Witness_isUnit
    (v : iutInitialThetaOddModSupportFinset D) :
    IsUnit (h1Witness D n v) := by
  rw [h1Witness_eq_canonicalWitness D n v]
  exact
    InitialThetaCanonicalTorsionPilotTensorLogShellBridge.canonicalWitness_isUnit D n v

end InitialThetaLocalH1LogTensorBridge

end
end JoshiTeich.Act1Scene1
