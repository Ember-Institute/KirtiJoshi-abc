import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-SCALAR-IMAGE
source: Joshi III `le:volume-lemma2/3`; actual canonical logarithm scalars.
fidelity: proves the actual region is the continuous tensor-scale image
of the unit integral lattice and expresses normalized Haar measure by
the resulting Haar character. Factor-norm/weight evaluation, maximal
order/hull and different-untilt theta identification remain open.
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

def scale : (packet D p c hc).Tensor ≃L[ℚ_[p]] (packet D p c hc).Tensor :=
  (packet D p c hc).continuousScale (fun i => InitialThetaLogWitness.value D (c i))
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i))

theorem region_eq_scaledUnitLattice :
    (region D p c hc : Set (packet D p c hc).Tensor) =
      (scale D p c hc) '' ((packet D p c hc).unitLattice : Set (packet D p c hc).Tensor) := by
  exact (LocalCompletion.Packet.unitLattice_image_scale (packet D p c hc)
    (fun i => InitialThetaLogWitness.value D (c i))
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i))).symm

theorem region_normalizedHaar_eq :
    (packet D p c hc).normalizedHaar (region D p c hc) =
      (distribHaarChar (packet D p c hc).Tensor (scale D p c hc) : ENNReal) := by
  exact LocalCompletion.Packet.normalizedHaar_scalarLattice (packet D p c hc)
    (fun i => InitialThetaLogWitness.value D (c i))
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i))

theorem region_normalizedHaar_pos_le_one :
    0 < (packet D p c hc).normalizedHaar (region D p c hc) ∧
      (packet D p c hc).normalizedHaar (region D p c hc) ≤ 1 := by
  constructor
  · rw [region_normalizedHaar_eq]
    exact ENNReal.coe_pos.mpr distribHaarChar_pos
  · exact (measure_mono (region_le_unitLattice D p c hc)).trans_eq
      (LocalCompletion.Packet.normalizedHaar_unitLattice (packet D p c hc))

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
