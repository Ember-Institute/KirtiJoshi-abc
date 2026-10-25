/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotPaperLogBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperWitnessTensorLogShell

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-PILOT-TENSOR-LOG-SHELL-BRIDGE
source: the canonical torsion pilot/paper-log bridge and the actual tensor
witness carrier from `IutInitialThetaPaperWitnessTensorLogShell.lean`.
fidelity: forms the pure tensor of canonical `j = 1` normalized logs over one
actual packet and proves that it is definitionally the existing paper witness.
The tensor log-shell and unit consequences are then inherited from the actual
witness carrier.
boundary: Scene1/Derived; this is an actual tensor-carrier identity. It does
not identify the tensor with H¹ₑ/BK data, a Frechet period, or a paper theta
locus.
-/

namespace InitialThetaCanonicalTorsionPilotTensorLogShellBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

local abbrev packet (v : iutInitialThetaOddModSupportFinset D) :=
  PaperLogWitnessHull.packet D n v

noncomputable def canonicalWitness
    (v : iutInitialThetaOddModSupportFinset D) : (packet D n v).Tensor :=
  (packet D n v).pure (fun i =>
    InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D
      (FullSupportThetaLogHull.sourceAt D n v i) 1)

structure Data (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ) : Type (u + 1) where
  witness_eq : ∀ v, canonicalWitness D n v = PaperLogWitnessHull.witness D n v
  mem_tensorLogShell : ∀ v, canonicalWitness D n v ∈ (packet D n v).tensorLogShell
  isUnit : ∀ v, IsUnit (canonicalWitness D n v)

noncomputable def canonical : Data D n where
  witness_eq v := by
    unfold canonicalWitness PaperLogWitnessHull.witness
    apply congrArg (packet D n v).pure
    funext i
    exact InitialThetaCanonicalTorsionPilotPaperLogBridge.canonical_value_eq_normalizedLog_one D
      (FullSupportThetaLogHull.sourceAt D n v i)
  mem_tensorLogShell v := by
    rw [canonicalWitness_eq_witness D n v]
    exact PaperLogWitnessHull.witness_mem_tensorLogShell D n v
  isUnit v := by
    rw [canonicalWitness_eq_witness D n v]
    exact PaperLogWitnessHull.witness_isUnit D n v

theorem canonicalWitness_eq_witness
    (v : iutInitialThetaOddModSupportFinset D) :
    canonicalWitness D n v = PaperLogWitnessHull.witness D n v :=
  (canonical D n).witness_eq v

theorem canonicalWitness_mem_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    canonicalWitness D n v ∈ (packet D n v).tensorLogShell :=
  (canonical D n).mem_tensorLogShell v

theorem canonicalWitness_isUnit
    (v : iutInitialThetaOddModSupportFinset D) :
    IsUnit (canonicalWitness D n v) :=
  (canonical D n).isUnit v

end InitialThetaCanonicalTorsionPilotTensorLogShellBridge

end
end JoshiTeich.Act1Scene1
