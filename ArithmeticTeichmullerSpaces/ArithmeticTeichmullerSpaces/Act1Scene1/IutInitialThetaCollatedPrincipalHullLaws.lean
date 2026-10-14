import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliCollatedNormalizationHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-COLLATED-PRINCIPAL-HULL-LAWS
source: Joshi III principal hull (3568--3574) and actual normalization span.
fidelity: proves the collated normalization span is the least principal hull
of the original union, including unions of zero Haar measure. Its integral
span has positive Haar by actual log generator coverage. Coverage and upper
containment remain explicit; no theta/Bloch-Kato identity is supplied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FixedModuliThetaCollatedHull
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
local instance principalCollationPrime : Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩
local instance principalCollationIntegralModule : Module ℤ_[Arithmetic.residueChar v.1]
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  Module.compHom (FixedModuliThetaTensor.packet D v σ hσ).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])
variable {κ : Type*}
variable (C : κ → Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor)

theorem collation_subset_region : (⋃ k, C k) ⊆ region D v σ hσ C :=
  (FixedModuliThetaTensor.packet D v σ hσ).subset_normalizationHull _

theorem region_le_principalRegion (a : (FixedModuliThetaTensor.packet D v σ hσ).Tensor)
    (hCa : (⋃ k, C k) ⊆ (FixedModuliThetaTensor.packet D v σ hσ).principalRegion a) :
    (region D v σ hσ C : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ⊆
      (FixedModuliThetaTensor.packet D v σ hσ).principalRegion a :=
  ((FixedModuliThetaTensor.packet D v σ hσ).normalizationHull_le_iff _
    ((FixedModuliThetaTensor.packet D v σ hσ).principalNormalizationModule a)).mpr hCa

theorem region_is_least_principal
    (hgen : (FixedModuliThetaTensor.packet D v σ hσ).scalarGenerators
      (fun i => iutInitialThetaFullQRootLogValue D (σ i)) ⊆ ⋃ k, C k)
    (hunit : ∀ k, C k ⊆ (FixedModuliThetaTensor.packet D v σ hσ).normalization) :
    ∃ a : (FixedModuliThetaTensor.packet D v σ hσ).Tensor,
      IsUnit a ∧ (region D v σ hσ C : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) =
        (FixedModuliThetaTensor.packet D v σ hσ).principalRegion a ∧
      (⋃ k, C k) ⊆ region D v σ hσ C ∧
      ∀ b : (FixedModuliThetaTensor.packet D v σ hσ).Tensor, IsUnit b →
        (⋃ k, C k) ⊆ (FixedModuliThetaTensor.packet D v σ hσ).principalRegion b →
        (region D v σ hσ C : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ⊆
          (FixedModuliThetaTensor.packet D v σ hσ).principalRegion b := by
  let U := (FixedModuliThetaTensor.packet D v σ hσ).integralHull (⋃ k, C k)
  let hU := integralHull_isBounded D v σ hσ C hunit
  let hpos := integralHull_haar_pos D v σ hσ C hgen
  refine ⟨(FixedModuliThetaTensor.packet D v σ hσ).hullMultiplier U hU hpos,
    (FixedModuliThetaTensor.packet D v σ hσ).hullMultiplier_isUnit U hU hpos,
    region_eq_leastHull D v σ hσ C hgen hunit, collation_subset_region D v σ hσ C, ?_⟩
  intro b _ hCb
  exact region_le_principalRegion D v σ hσ C b hCb

end
end JoshiTeich.Act1Scene1.FixedModuliThetaCollatedHull
