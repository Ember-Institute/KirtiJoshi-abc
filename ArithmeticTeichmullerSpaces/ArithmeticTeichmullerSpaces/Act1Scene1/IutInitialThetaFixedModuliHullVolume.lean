import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarHullVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliTensorVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorVolumeMonotonicity

/-!
source-id: JT-SCENE1-INITIAL-THETA-FIXED-MODULI-LEAST-HULL-VOLUME
source: actual fixed-moduli ordinary log tensor and chosen least principal
hull; Joshi III contained-region estimate (3624--3631).
fidelity: derives a lower bound for the actual normalization-Haar degree
volume of any bounded positive-Haar hull containing the actual log tensor
lattice. No theta locus, Bloch-Kato/untilt witness or paper norm identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FixedModuliThetaHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (v : iutInitialThetaOddModSupportFinset D)
variable {ι : Type} [Fintype ι]
variable (σ : ι → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ i, Ideal.LiesOver (σ i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance hullPrime : Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩
local instance actualHullIntegralModule : Module ℤ_[Arithmetic.residueChar v.1]
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  Module.compHom (FixedModuliThetaTensor.packet D v σ hσ).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])
variable (U : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor)
variable (hU : Bornology.IsBounded U)
variable (hpos : 0 < (FixedModuliThetaTensor.packet D v σ hσ).normalizationHaar U)

def volume : ℝ :=
  (FixedModuliThetaTensor.packet D v σ hσ).normalizationDegreeVolume
    ((FixedModuliThetaTensor.packet D v σ hσ).leastHull U hU hpos) ^ Arithmetic.localDeg v.1

theorem relativeFactor_pow_le_volume
    (hregion : (FixedModuliThetaTensor.region D v σ hσ :
      Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ⊆ U) :
    iutInitialThetaRelativeQRootFactor D v ^ Fintype.card ι ≤ volume D v σ hσ U hU hpos := by
  have hz : ∀ i, iutInitialThetaFullQRootLogValue D (σ i) ≠ 0 := by
    intro i
    apply norm_ne_zero_iff.mp
    rw [iutInitialThetaFullQRootLogValue_norm_eq]
    exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)
  have h := (FixedModuliThetaTensor.packet D v σ hσ).degreeVolume_scalarLattice_le_leastHullVolume
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) hz U hU hpos hregion
  have hpow := pow_le_pow_left₀
    ((FixedModuliThetaTensor.packet D v σ hσ).degreeVolume_nonneg
      (FixedModuliThetaTensor.region D v σ hσ)) h (Arithmetic.localDeg v.1)
  change FixedModuliThetaTensor.volume D v σ hσ ≤ volume D v σ hσ U hU hpos at hpow
  rw [FixedModuliThetaTensor.volume_eq_relativeFactor_pow] at hpow
  exact hpow

end
end JoshiTeich.Act1Scene1.FixedModuliThetaHull
