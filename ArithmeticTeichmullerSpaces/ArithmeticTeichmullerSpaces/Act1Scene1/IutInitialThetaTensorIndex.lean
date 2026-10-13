import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorScale
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndex

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-INTEGRAL-INDEX
fidelity: computes actual q-root logarithm tensor-region normalized Haar
measure as the inverse of its finite additive index in the unit integral
tensor lattice. Factor-norm/weight evaluation and hull remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTensorWitness

open JoshiTeich.Prologue NumberField MeasureTheory

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι]
variable (c : ι → (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset)
variable (hc : ∀ i, Arithmetic.residueChar (c i).1 = p)

def regionIndex : ℕ :=
  (packet D p c hc).scalarIndex (fun i => InitialThetaLogWitness.value D (c i))

theorem regionIndex_pos : 0 < regionIndex D p c hc :=
  LocalCompletion.Packet.scalarIndex_pos (packet D p c hc) _
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i))

set_option maxHeartbeats 1000000 in
theorem region_normalizedHaar_eq_inv_index :
    (packet D p c hc).normalizedHaar (region D p c hc) = (regionIndex D p c hc : ENNReal)⁻¹ := by
  have hz1 (i : ι) : ‖InitialThetaLogWitness.value D (c i)‖ ≤ 1 := by
    rw [InitialThetaLogWitness.norm_value_eq_qroot_norm D (c i)]
    exact (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D (c i)).le
  exact LocalCompletion.Packet.normalizedHaar_scalarLattice_eq_inv_index (packet D p c hc)
    (fun i => InitialThetaLogWitness.value D (c i))
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i)) hz1

theorem regionIndex_haar_product_eq_one :
    (regionIndex D p c hc : ENNReal) * (packet D p c hc).normalizedHaar (region D p c hc) = 1 := by
  rw [region_normalizedHaar_eq_inv_index]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (regionIndex_pos D p c hc).ne')
    (ENNReal.natCast_ne_top _)

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
