/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLocalH1LogTensorBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperWitnessTensorLogShell

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

set_option maxHeartbeats 1000000

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-LOCAL-H1-LOG-TENSOR-HULL-BRIDGE
source: the local H¹/log tensor witness and the actual paper-witness tensor
hull laws in `IutInitialThetaPaperWitnessTensorLogShell.lean`.
fidelity: transports log-shell containment, normalization-hull equality, and
actual finite/global negative-log bounds from the paper witness to the tensor
formed from the local actual H¹/log source.
boundary: Scene1/Derived; the results concern the actual tensor hull. They do
not identify it with H¹ₑ/BK data or the paper `thetaVolume`.
-/

namespace InitialThetaLocalH1LogTensorHullBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

abbrev packet (v : iutInitialThetaOddModSupportFinset D) :=
  PaperLogWitnessHull.packet D n v

local instance paperTensorPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

theorem h1Witness_integralHull_le_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull
        {InitialThetaLocalH1LogTensorBridge.h1Witness D n v} ≤
      (packet D n v).tensorLogShell := by
  rw [InitialThetaLocalH1LogTensorBridge.h1Witness_eq_paperWitness D n v]
  exact PaperLogWitnessHull.witness_integralHull_le_tensorLogShell D n v

theorem h1Witness_integralHull_normalizationHull_eq_base
    (v : iutInitialThetaOddModSupportFinset D) :
    ((packet D n v).normalizationHull
        ((packet D n v).integralHull
          {InitialThetaLocalH1LogTensorBridge.h1Witness D n v}) :
      Set (packet D n v).Tensor) =
      (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor) := by
  rw [InitialThetaLocalH1LogTensorBridge.h1Witness_eq_paperWitness D n v]
  exact PaperLogWitnessHull.witness_integralHull_normalizationHull_eq_base D n v

theorem h1Witness_globalVolume_negLog_ge_mul_referenceAbsLogQ :
    -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull
                {InitialThetaLocalH1LogTensorBridge.h1Witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) ≥
      (n : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  simp_rw [InitialThetaLocalH1LogTensorBridge.h1Witness_eq_paperWitness D n]
  exact PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_ge_mul_referenceAbsLogQ D n

theorem h1Witness_globalVolume_negLog_nonneg :
    0 ≤ -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull
                {InitialThetaLocalH1LogTensorBridge.h1Witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) := by
  simp_rw [InitialThetaLocalH1LogTensorBridge.h1Witness_eq_paperWitness D n]
  exact PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_nonneg D n

theorem h1Witness_globalVolume_selectedPaperRootProduct_pow_lt
    (hn : 0 < n) :
    actualSelectedPaperRootNormProduct D ^ n <
      ((∏ v : iutInitialThetaOddModSupportFinset D,
        (packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull
              {InitialThetaLocalH1LogTensorBridge.h1Witness D n v})) ^ Arithmetic.localDeg v.1) ^
        (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) := by
  simp_rw [InitialThetaLocalH1LogTensorBridge.h1Witness_eq_paperWitness D n]
  exact PaperLogWitnessHull.witness_integralHull_globalVolume_selectedPaperRootProduct_pow_lt D n hn

end InitialThetaLocalH1LogTensorHullBridge

end
end JoshiTeich.Act1Scene1
