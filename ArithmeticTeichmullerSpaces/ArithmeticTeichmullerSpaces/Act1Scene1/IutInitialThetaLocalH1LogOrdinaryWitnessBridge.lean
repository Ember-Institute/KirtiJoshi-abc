/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLocalH1LogTensorBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCollation

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

set_option maxHeartbeats 1000000

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-LOCAL-H1-LOG-ORDINARY-WITNESS-BRIDGE
source: the local actual H¹/log source, the paper `p*` normalization, and the
ordinary Kummer-log witness from `IutInitialThetaOrdinaryLogHullVolume.lean`.
fidelity: multiplies each local H¹/log normalized value by the explicit
paper scale and proves equality with the existing ordinary witness. The
ordinary singleton region and its corrected volume laws are then available
for the H¹/log source.
boundary: Scene1/Derived; this remains an actual ordinary-log carrier result.
It does not identify the carrier with H¹ₑ/BK data or the paper theta locus.
-/

namespace InitialThetaLocalH1LogOrdinaryWitnessBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

abbrev packet (v : iutInitialThetaOddModSupportFinset D) :=
  OrdinaryKummerLogHull.packet D n v

local instance bridgePrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

local instance bridgeSourcePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance bridgeCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

local instance bridgeAlgebra
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (PrincipalUnitKummer.localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl

local instance bridgeContinuousSMul
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1]
      (PrincipalUnitKummer.localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

noncomputable def h1OrdinaryWitness
    (v : iutInitialThetaOddModSupportFinset D) : (packet D n v).Tensor :=
  (packet D n v).pure (fun i =>
    (LocalPadicLog.paperScale
      (Arithmetic.residueChar (FullSupportThetaLogHull.sourceAt D n v i).1) :
      (packet D n v).Factor i) *
      (InitialThetaLocalH1LogSource.canonical D
        (FullSupportThetaLogHull.sourceAt D n v i)).normalizedLog)

theorem h1OrdinaryWitness_eq_witness
    (v : iutInitialThetaOddModSupportFinset D) :
    h1OrdinaryWitness D n v = OrdinaryKummerLogHull.witness D n v := by
  unfold h1OrdinaryWitness OrdinaryKummerLogHull.witness OrdinaryKummerLogHull.scalar
  apply congrArg (packet D n v).pure
  funext i
  rw [InitialThetaLocalH1LogSource.canonical_normalizedLog_eq D]
  exact (OrdinaryKummerLogHull.scalar_eq_scale_value D _).symm

theorem h1OrdinaryWitness_isUnit
    (v : iutInitialThetaOddModSupportFinset D) :
    IsUnit (h1OrdinaryWitness D n v) := by
  rw [h1OrdinaryWitness_eq_witness D n v]
  exact (packet D n v).pure_isUnit _ (fun i => OrdinaryKummerLogHull.scalar_ne_zero D _)

theorem h1OrdinaryRegion_eq_region
    (v : iutInitialThetaOddModSupportFinset D) :
    ((packet D n v).normalizationHull {h1OrdinaryWitness D n v} :
      Set (packet D n v).Tensor) =
      (OrdinaryKummerLogHull.region D n v : Set (packet D n v).Tensor) := by
  rw [h1OrdinaryWitness_eq_witness D n v]
  rfl

theorem h1OrdinaryRegion_isCompact
    (v : iutInitialThetaOddModSupportFinset D) :
    IsCompact (OrdinaryKummerLogHull.region D n v :
      Set (packet D n v).Tensor) :=
  OrdinaryKummerLogHull.region_isCompact D n v

theorem h1OrdinaryRegion_degreeVolume_eq_corrected
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull {h1OrdinaryWitness D n v}) =
      OrdinaryKummerLogHull.degreeCorrection D n v *
        (packet D n v).normalizationDegreeVolume
          (FullSupportThetaLogHull.region D n v) := by
  rw [h1OrdinaryRegion_eq_region D n v]
  exact OrdinaryKummerLogHull.region_degreeVolume_eq_corrected D n v

end InitialThetaLocalH1LogOrdinaryWitnessBridge

end
end JoshiTeich.Act1Scene1
