import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHullNormalizationBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorVolumeMonotonicity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliTensorVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-COLLATED-NORMALIZATION-HULL
source: actual fixed-moduli log tensor generators and Joshi III contained
region estimate (3624--3631), using the principal hull of 3568--3574.
fidelity: constructs a collated normalization-module hull and proves it is
the actual least principal hull of the integral span of the collation.
Generator coverage and containment in normalization imply compactness,
positive finite Haar and the canonical relative root volume lower bound.
They remain explicit geometric inputs; no theta/Bloch-Kato source is supplied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FixedModuliThetaCollatedHull
open JoshiTeich.Prologue MeasureTheory
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
local instance collatedNormPrime : Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩
local instance collatedNormIntegralModule : Module ℤ_[Arithmetic.residueChar v.1]
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  Module.compHom (FixedModuliThetaTensor.packet D v σ hσ).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])
variable {κ : Type*}
variable (C : κ → Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor)

def region : Submodule (FixedModuliThetaTensor.packet D v σ hσ).normalization
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  (FixedModuliThetaTensor.packet D v σ hσ).normalizationHull (⋃ k, C k)

def volume : ℝ :=
  (FixedModuliThetaTensor.packet D v σ hσ).normalizationDegreeVolume (region D v σ hσ C) ^
    Arithmetic.localDeg v.1

theorem integralHull_subset_normalization
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    ((FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k) :
      Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ⊆
      (FixedModuliThetaTensor.packet D v σ hσ).normalization :=
  ((FixedModuliThetaTensor.packet D v σ hσ).integralHull_le_iff _
    (FixedModuliThetaTensor.packet D v σ hσ).normalization.toSubmodule).mpr
      (Set.iUnion_subset hunit)

theorem integralHull_isBounded
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    Bornology.IsBounded
      ((FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k) :
        Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) :=
  (FixedModuliThetaTensor.packet D v σ hσ).normalization_isCompact.isBounded.subset
    (integralHull_subset_normalization D v σ hσ C hunit)

variable (hgen : (FixedModuliThetaTensor.packet D v σ hσ).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ i)) ⊆ ⋃ k, C k)

include hgen in
theorem scalarLattice_le_integralHull :
    FixedModuliThetaTensor.region D v σ hσ ≤
      (FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k) :=
  (FixedModuliThetaTensor.packet D v σ hσ).scalarLattice_le_integralHull _ _ hgen

private theorem logScalar_ne_zero (i : ι) : iutInitialThetaFullQRootLogValue D (σ i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)

include hgen in
theorem integralHull_haar_pos :
    0 < (FixedModuliThetaTensor.packet D v σ hσ).normalizationHaar
      ((FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k)) :=
  ((FixedModuliThetaTensor.packet D v σ hσ).scalarLattice_normalizationHaar_pos
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) (logScalar_ne_zero D σ)).trans_le
      (measure_mono (scalarLattice_le_integralHull D v σ hσ C hgen))

include hgen in
theorem region_eq_leastHull
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    (region D v σ hσ C : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) =
      (FixedModuliThetaTensor.packet D v σ hσ).leastHull
        ((FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k))
        (integralHull_isBounded D v σ hσ C hunit) (integralHull_haar_pos D v σ hσ C hgen) := by
  rw [region, ← (FixedModuliThetaTensor.packet D v σ hσ).normalizationHull_integralHull]
  exact (FixedModuliThetaTensor.packet D v σ hσ).normalizationHull_eq_leastHull _ _ _

include hgen in
theorem region_isCompact
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    IsCompact (region D v σ hσ C : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) := by
  rw [region_eq_leastHull D v σ hσ C hgen hunit]
  exact (FixedModuliThetaTensor.packet D v σ hσ).leastHull_isCompact _ _ _

include hgen in
theorem region_haar_pos_lt_top
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    0 < (FixedModuliThetaTensor.packet D v σ hσ).normalizationHaar (region D v σ hσ C) ∧
      (FixedModuliThetaTensor.packet D v σ hσ).normalizationHaar (region D v σ hσ C) < ⊤ := by
  rw [region_eq_leastHull D v σ hσ C hgen hunit]
  exact (FixedModuliThetaTensor.packet D v σ hσ).leastHull_haar_pos_lt_top _ _ _

include hgen in
theorem relativeFactor_pow_le_volume
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    iutInitialThetaRelativeQRootFactor D v ^ Fintype.card ι ≤ volume D v σ hσ C := by
  have h := (FixedModuliThetaTensor.packet D v σ hσ).degreeVolume_scalarLattice_le_leastHullVolume
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) (logScalar_ne_zero D σ)
    ((FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k))
    (integralHull_isBounded D v σ hσ C hunit) (integralHull_haar_pos D v σ hσ C hgen)
    (scalarLattice_le_integralHull D v σ hσ C hgen)
  rw [← region_eq_leastHull D v σ hσ C hgen hunit] at h
  have hpow := pow_le_pow_left₀
    ((FixedModuliThetaTensor.packet D v σ hσ).degreeVolume_nonneg
      (FixedModuliThetaTensor.region D v σ hσ)) h (Arithmetic.localDeg v.1)
  change FixedModuliThetaTensor.volume D v σ hσ ≤ volume D v σ hσ C at hpow
  rw [FixedModuliThetaTensor.volume_eq_relativeFactor_pow] at hpow
  exact hpow

theorem volume_le_one
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    volume D v σ hσ C ≤ 1 := by
  unfold volume
  have hsub : (region D v σ hσ C :
      Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ⊆
        (FixedModuliThetaTensor.packet D v σ hσ).normalization :=
    (FixedModuliThetaTensor.packet D v σ hσ).normalizationHull_subset_normalization
      (⋃ k, C k) (Set.iUnion_subset hunit)
  have hupper := (FixedModuliThetaTensor.packet D v σ hσ).normalizationDegreeVolume_le_one
    (region D v σ hσ C) hsub
  exact pow_le_one₀ (Real.rpow_nonneg ENNReal.toReal_nonneg _) hupper

end
end JoshiTeich.Act1Scene1.FixedModuliThetaCollatedHull
