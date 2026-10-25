/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionPilotSaturatedKummerLogBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLocalH1LogSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

set_option maxHeartbeats 1000000

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-PILOT-LOCAL-H1-LOG-BRIDGE
source: the local actual H¹/log source and the canonical torsion pilot plus
saturated-Kummer source packages.
fidelity: proves that the normalized log field of the local actual H¹/log
source is the same value as the canonical torsion `j = 1` normalized log and
the saturated Kummer image log. The already proved paper witness identity is
also exposed on this common carrier.
boundary: Scene1/Derived; this is a local source-consistency package. It does
not identify the ambient carrier with H¹ₑ, crystalline cohomology, or a
Bloch--Kato comparison.
-/

namespace InitialThetaCanonicalTorsionPilotLocalH1LogBridge

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance bridgePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance bridgeCharZero : CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance bridgeAlgebra : Algebra ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance bridgeContinuousSMul : ContinuousSMul ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

theorem canonical_h1_normalizedLog_eq_torsion_normalizedLog :
    (InitialThetaLocalH1LogSource.canonical D s).normalizedLog =
      InitialThetaCanonicalTorsionPilotLogShellSource.normalizedLog D s 1 := by
  rw [InitialThetaLocalH1LogSource.canonical_normalizedLog_eq D s]
  exact
    (InitialThetaCanonicalTorsionPilotPaperLogBridge.canonical_normalizedLog_one_eq_value D s).symm

theorem canonical_h1_normalizedLog_eq_saturatedImageLog :
    (InitialThetaLocalH1LogSource.canonical D s).normalizedLog =
      LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (PrincipalUnitKummer.normalizedSaturatedClass D s) := by
  rw [InitialThetaLocalH1LogSource.canonical_normalizedLog_eq D s]
  exact (PrincipalUnitKummer.normalizedSaturatedClass_saturatedImageLog_eq_value D s).symm

theorem canonical_h1_normalizedLog_eq_paperValue :
    (InitialThetaLocalH1LogSource.canonical D s).normalizedLog =
      PaperLogWitnessHull.value D s :=
  InitialThetaLocalH1LogSource.canonical_normalizedLog_eq D s

theorem canonical_h1_normalizedLog_ne_zero :
    (InitialThetaLocalH1LogSource.canonical D s).normalizedLog ≠ 0 := by
  rw [canonical_h1_normalizedLog_eq_paperValue D s]
  exact PaperLogWitnessHull.value_ne_zero D s

end InitialThetaCanonicalTorsionPilotLocalH1LogBridge

end
end JoshiTeich.Act1Scene1
