import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorIndex
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralBasis

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-INTEGRAL-BASIS
fidelity: derives finite generation of the actual q-root logarithm tensor
region from its bounded integral coordinates. Generic lattice free/span
lemmas live in the companion module, while the actual region free module,
integral basis, tensor index evaluation, weighted volume and hull remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTensorWitness

open JoshiTeich.Prologue NumberField

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι]
variable (c : ι → (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset)
variable (hc : ∀ i, Arithmetic.residueChar (c i).1 = p)

theorem region_module_finite : Module.Finite ℤ_[p] (region D p c hc) := by
  let P := packet D p c hc
  rw [region_eq_ballLattice]
  exact LocalCompletion.Packet.bounded_module_finite P _
    (LocalCompletion.Packet.unitLattice_isBounded P |>.subset
      (LocalCompletion.Packet.lattice_mono P (fun i => Metric.closedBall_subset_closedBall
        ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D (c i)).le))))

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
