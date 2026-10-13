import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionRepeatedPacketVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedLogBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootChoice

/-!
source-id: JT-SCENE1-INITIAL-THETA-REPEATED-ROOT-HAAR
source: Joshi III th:moccor-Mochizuki-form2 (3624--3631), fixed-place tensor
organization, actual ordinary log balls and dimension-normalized tensor Haar.
fidelity: repeats one actual completion/log scalar over Fin n. Raising its
degree volume to the moduli local degree computes the n-th power of the actual
relative root factor. This ordinary repeated packet does not construct the
paper's different untilts, Bloch-Kato classes, maximal order or theta hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.RepeatedThetaRoot
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ)

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

abbrev packet := LocalCompletion.Packet.repeatedPacket s.1
  (show Arithmetic.residueChar s.1 = Arithmetic.residueChar s.1 from rfl) n

local instance integralModule : Module ℤ_[Arithmetic.residueChar s.1] (packet D s n).Tensor :=
  Module.compHom (packet D s n).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar s.1] ℚ_[Arithmetic.residueChar s.1])

def region : Submodule ℤ_[Arithmetic.residueChar s.1] (packet D s n).Tensor :=
  (packet D s n).scalarLattice (fun _ => iutInitialThetaFullQRootLogValue D s)

def moduliVolume
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) : ℝ :=
  (packet D s n).degreeVolume (region D s n) ^ Arithmetic.localDeg v

private theorem logScalar_ne_zero : iutInitialThetaFullQRootLogValue D s ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)

theorem region_degreeVolume_eq_rootNorm :
    (packet D s n).degreeVolume (region D s n) =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
        ((n : ℝ) / Arithmetic.localDeg s.1) := by
  have hn : ‖iutInitialThetaFullQRootLogValue D s‖ < 1 := by
    rw [iutInitialThetaFullQRootLogValue_norm_eq]
    exact iutInitialThetaFullQRoot_norm_lt_one D s
  have h := LocalCompletion.Packet.repeatedPacket_degreeVolume_eq s.1 rfl n
    (iutInitialThetaFullQRootLogValue D s) (logScalar_ne_zero D s) hn
  change (packet D s n).degreeVolume (region D s n) =
    ‖iutInitialThetaFullQRootLogValue D s‖ ^ ((n : ℝ) / Arithmetic.localDeg s.1) at h
  simpa only [iutInitialThetaFullQRootLogValue_norm_eq] using h

theorem moduliVolume_eq_relativeFactor_pow
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    moduliVolume D s n v = iutInitialThetaRelativeQRootFactorAt D v s ^ n := by
  rw [moduliVolume, region_degreeVolume_eq_rootNorm, iutInitialThetaRelativeQRootFactorAt]
  rw [← Real.rpow_natCast _ (Arithmetic.localDeg v), ← Real.rpow_natCast _ n,
    ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

theorem moduliVolume_pos
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    0 < moduliVolume D s n v := by
  rw [moduliVolume_eq_relativeFactor_pow]
  exact pow_pos (iutInitialThetaRelativeQRootFactorAt_mem_Ioo D v s).1 n

end
end JoshiTeich.Act1Scene1.RepeatedThetaRoot
