import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarNormalization
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliTensorVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-FIXED-MODULI-NORMALIZATION-VOLUME
source: actual fixed-moduli relative-weight scalar region and its proved
normalization enlargement/Haar law.
fidelity: constructs the normalization enlargement of the actual ordinary
log tensor region and proves its corrected normalization-Haar volume is the
canonical relative root factor to the tuple cardinality. Changing legal
over-places preserves this real volume. No paper untilt/theta hull identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FixedModuliThetaNormalization
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
local instance normalizedPrime : Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩
local instance normalizedIntegralModule : Module ℤ_[Arithmetic.residueChar v.1]
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  Module.compHom (FixedModuliThetaTensor.packet D v σ hσ).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])

private theorem logScalar_ne_zero (i : ι) : iutInitialThetaFullQRootLogValue D (σ i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)

def region : Submodule ℤ_[Arithmetic.residueChar v.1]
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  (FixedModuliThetaTensor.packet D v σ hσ).scalarNormalization
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) (logScalar_ne_zero D σ)

def volume : ℝ :=
  (FixedModuliThetaTensor.packet D v σ hσ).normalizationDegreeVolume (region D v σ hσ) ^
    Arithmetic.localDeg v.1

theorem volume_eq_unitVolume : volume D v σ hσ = FixedModuliThetaTensor.volume D v σ hσ := by
  rw [volume, region,
    (FixedModuliThetaTensor.packet D v σ hσ).normalizationDegreeVolume_scalarNormalization_eq_degreeVolume]
  rfl

theorem volume_eq_relativeFactor_pow :
    volume D v σ hσ = iutInitialThetaRelativeQRootFactor D v ^ Fintype.card ι := by
  rw [volume_eq_unitVolume, FixedModuliThetaTensor.volume_eq_relativeFactor_pow]

theorem volume_choice_independent
    (τ : ι → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hτ : ∀ i, Ideal.LiesOver (τ i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    volume D v σ hσ = volume D v τ hτ := by
  rw [volume_eq_relativeFactor_pow, volume_eq_relativeFactor_pow]

end
end JoshiTeich.Act1Scene1.FixedModuliThetaNormalization
