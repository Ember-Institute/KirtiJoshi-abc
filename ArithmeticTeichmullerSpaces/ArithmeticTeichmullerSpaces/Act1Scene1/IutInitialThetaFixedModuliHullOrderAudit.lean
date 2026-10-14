import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHullOrderAudit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliTensorVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-FIXED-MODULI-HULL-ORDER-AUDIT
source: actual fixed-moduli ordinary log scalar lattice and Joshi III
pr:convexes-and-hulls (3597--3609).
fidelity: constructs the actual log region hull without boundedness or Haar
certificates as inputs, and proves its equality with the integral-module
hull is equivalent to normalization mass one (or equality of the orders).
This is a criterion, not a constructed counterexample to the paper or an
identification of ordinary logarithms with Bloch-Kato theta loci.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FixedModuliThetaHullOrder
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
local instance actualOrderPrime : Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩
local instance actualOrderIntegralModule : Module ℤ_[Arithmetic.residueChar v.1]
    (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  Module.compHom (FixedModuliThetaTensor.packet D v σ hσ).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])

private theorem logScalar_ne_zero (i : ι) : iutInitialThetaFullQRootLogValue D (σ i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)

theorem region_isCompact : IsCompact (FixedModuliThetaTensor.region D v σ hσ :
    Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) :=
  (FixedModuliThetaTensor.packet D v σ hσ).scalarLattice_isCompact_of_nonzero
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) (logScalar_ne_zero D σ)

theorem region_normalizationHaar_pos :
    0 < (FixedModuliThetaTensor.packet D v σ hσ).normalizationHaar
      (FixedModuliThetaTensor.region D v σ hσ) :=
  (FixedModuliThetaTensor.packet D v σ hσ).scalarLattice_normalizationHaar_pos
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) (logScalar_ne_zero D σ)

def regionHull : Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor :=
  (FixedModuliThetaTensor.packet D v σ hσ).leastHull
    (FixedModuliThetaTensor.region D v σ hσ) (region_isCompact D v σ hσ).isBounded
    (region_normalizationHaar_pos D v σ hσ)

theorem regionHull_eq_integralHull_iff_order_eq :
    regionHull D v σ hσ =
        ((FixedModuliThetaTensor.packet D v σ hσ).integralHull
          (FixedModuliThetaTensor.region D v σ hσ) :
          Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ↔
      (FixedModuliThetaTensor.packet D v σ hσ).normalization.toSubmodule =
        (FixedModuliThetaTensor.packet D v σ hσ).unitLattice :=
  (FixedModuliThetaTensor.packet D v σ hσ).leastHull_scalarLattice_eq_integralHull_iff
    (fun i => iutInitialThetaFullQRootLogValue D (σ i)) (logScalar_ne_zero D σ)
    (region_isCompact D v σ hσ).isBounded (region_normalizationHaar_pos D v σ hσ)

theorem regionHull_eq_integralHull_iff_mass_eq_one :
    regionHull D v σ hσ =
        ((FixedModuliThetaTensor.packet D v σ hσ).integralHull
          (FixedModuliThetaTensor.region D v σ hσ) :
          Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) ↔
      (FixedModuliThetaTensor.packet D v σ hσ).normalizationMass = 1 :=
  (regionHull_eq_integralHull_iff_order_eq D v σ hσ).trans
    (FixedModuliThetaTensor.packet D v σ hσ).normalizationMass_eq_one_iff.symm

theorem regionHull_ne_integralHull_of_mass_ne_one
    (hne : (FixedModuliThetaTensor.packet D v σ hσ).normalizationMass ≠ 1) :
    regionHull D v σ hσ ≠
      ((FixedModuliThetaTensor.packet D v σ hσ).integralHull
        (FixedModuliThetaTensor.region D v σ hσ) :
        Set (FixedModuliThetaTensor.packet D v σ hσ).Tensor) :=
  fun h => hne ((regionHull_eq_integralHull_iff_mass_eq_one D v σ hσ).mp h)

end
end JoshiTeich.Act1Scene1.FixedModuliThetaHullOrder
