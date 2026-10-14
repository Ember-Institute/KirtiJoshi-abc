import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorVolumePower
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedLogBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootChoice

/-!
source-id: JT-SCENE1-INITIAL-THETA-FIXED-MODULI-TENSOR-VOLUME
source: Joshi III eq:weights (3554--3557), actual relative completion
degrees and local Haar, fixed-D root factor choice independence.
fidelity: tensors any finite tuple of actual over-places of one moduli
place. Common moduli local degree makes the inverse relative-finrank raw
norm product an actual region volume. Actual ordinary log scalars give
the canonical relative root factor to the tuple cardinality, independent
of legal over-place choices. Different untilts, Bloch-Kato classes,
paper norm/maximal order and theta-volume identities remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FixedModuliThetaTensor
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (v : iutInitialThetaOddModSupportFinset D)
variable {ι : Type} [Fintype ι]
variable (σ : ι → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ i, Ideal.LiesOver (σ i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)

local instance fixedPrime : Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

abbrev packet : LocalCompletion.Packet ↥D.prime.torsionField (Arithmetic.residueChar v.1) ι :=
  ⟨fun i => (σ i).1, fun i => Arithmetic.residueChar_eq_of_liesOver (hσ i)⟩

local instance fixedIntegralModule :
    Module ℤ_[Arithmetic.residueChar v.1] (packet D v σ hσ).Tensor :=
  Module.compHom (packet D v σ hσ).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])

def weight (i : ι) : ℝ :=
  letI := LocalCompletion.relativeAlgebra (hσ i)
  1 / (Module.finrank
    (LocalCompletion.completionAt ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) v.1)
    (LocalCompletion.completionAt ↥D.prime.torsionField (σ i).1) : ℝ)

theorem weight_eq_localDeg_ratio (i : ι) :
    weight D v σ hσ i = (Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg (σ i).1 :=
  LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio (hσ i)

theorem weight_mem_Ioc (i : ι) : weight D v σ hσ i ∈ Set.Ioc (0 : ℝ) 1 :=
  LocalCompletion.inverse_relativeFinrank_mem_Ioc (hσ i)

def scalarVolume (z : ∀ i, (packet D v σ hσ).Factor i) : ℝ :=
  (packet D v σ hσ).degreeVolume ((packet D v σ hσ).scalarLattice z) ^ Arithmetic.localDeg v.1

theorem scalarVolume_eq_weightedNorm_product
    (z : ∀ i, (packet D v σ hσ).Factor i)
    (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    scalarVolume D v σ hσ z = ∏ i, ‖z i‖ ^ weight D v σ hσ i := by
  rw [scalarVolume,
    (packet D v σ hσ).degreeVolume_scalarLattice_pow_eq_norm_product _ z hz hz1]
  apply Finset.prod_congr rfl
  intro i _
  rw [weight_eq_localDeg_ratio]

def region : Submodule ℤ_[Arithmetic.residueChar v.1] (packet D v σ hσ).Tensor :=
  (packet D v σ hσ).scalarLattice (fun i => iutInitialThetaFullQRootLogValue D (σ i))

def volume : ℝ :=
  (packet D v σ hσ).degreeVolume (region D v σ hσ) ^ Arithmetic.localDeg v.1

private theorem logScalar_ne_zero (i : ι) : iutInitialThetaFullQRootLogValue D (σ i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)

private theorem logScalar_contracting (i : ι) : ‖iutInitialThetaFullQRootLogValue D (σ i)‖ < 1 := by
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact iutInitialThetaFullQRoot_norm_lt_one D _

theorem volume_eq_relativeFactor_pow :
    volume D v σ hσ = iutInitialThetaRelativeQRootFactor D v ^ Fintype.card ι := by
  have h := (packet D v σ hσ).degreeVolume_scalarLattice_pow_eq_norm_product
    (Arithmetic.localDeg v.1) (fun i => iutInitialThetaFullQRootLogValue D (σ i))
    (logScalar_ne_zero D σ) (logScalar_contracting D σ)
  change volume D v σ hσ = ∏ i, ‖iutInitialThetaFullQRootLogValue D (σ i)‖ ^
    ((Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg (σ i).1) at h
  rw [h]
  simp only [iutInitialThetaFullQRootLogValue_norm_eq]
  change (∏ i, iutInitialThetaRelativeQRootFactorAt D v.1 (σ i)) = _
  have heq : ∀ i, iutInitialThetaRelativeQRootFactorAt D v.1 (σ i) =
      iutInitialThetaRelativeQRootFactor D v := fun i =>
    iutInitialThetaRelativeQRootFactorAt_eq_selectedFactor D v (σ i) (hσ i)
  simp only [heq, Finset.prod_const, Finset.card_univ]

theorem volume_pos : 0 < volume D v σ hσ := by
  rw [volume_eq_relativeFactor_pow]
  exact pow_pos (iutInitialThetaRelativeQRootFactor_mem_Ioo D v).1 _

theorem volume_choice_independent
    (τ : ι → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hτ : ∀ i, Ideal.LiesOver (τ i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    volume D v σ hσ = volume D v τ hτ := by
  rw [volume_eq_relativeFactor_pow, volume_eq_relativeFactor_pow]

end
end JoshiTeich.Act1Scene1.FixedModuliThetaTensor
