import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorIntegralBasis
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarScaling

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-HAAR-DIMENSION-SCALING
fidelity: computes the actual normalized Haar measure of the canonical
tensor region after multiplication by p. The exponent is the product of
the actual completion dimensions. This is the prime-scalar normalization
step, not the general determinant or paper weighted-volume formula.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTensorWitness

open JoshiTeich.Prologue NumberField MeasureTheory
open scoped BigOperators

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι]
variable (c : ι → (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset)
variable (hc : ∀ i, Arithmetic.residueChar (c i).1 = p)

local instance haarFactorAlgebra (i : ι) : Algebra ℚ_[p] ((packet D p c hc).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p c hc).residueChar_eq i)
local instance haarFactorFinite (i : ι) : Module.Finite ℚ_[p] ((packet D p c hc).Factor i) :=
  LocalCompletion.finite_padicAlgebra ((packet D p c hc).residueChar_eq i)

theorem region_haar_image_smul_padic :
    (packet D p c hc).normalizedHaar
      ((fun x : (packet D p c hc).Tensor => (p : ℚ_[p]) • x) ''
        (region D p c hc : Set (packet D p c hc).Tensor)) =
      ((p : ENNReal) ^ Module.finrank ℚ_[p] (packet D p c hc).Tensor)⁻¹ *
        (packet D p c hc).normalizedHaar (region D p c hc) :=
  PadicHaar.measure_image_smul_padic (packet D p c hc).normalizedHaar
    (region_isCompact D p c hc).measurableSet

theorem region_haar_image_smul_padic_factor_prod :
    (packet D p c hc).normalizedHaar
      ((fun x : (packet D p c hc).Tensor => (p : ℚ_[p]) • x) ''
        (region D p c hc : Set (packet D p c hc).Tensor)) =
      ((p : ENNReal) ^ (∏ i, Module.finrank ℚ_[p] ((packet D p c hc).Factor i)))⁻¹ *
        (packet D p c hc).normalizedHaar (region D p c hc) := by
  rw [region_haar_image_smul_padic, LocalCompletion.Packet.tensor_finrank_eq_factor_prod]

theorem region_haar_image_smul_padic_eq_inv_index :
    (packet D p c hc).normalizedHaar
      ((fun x : (packet D p c hc).Tensor => (p : ℚ_[p]) • x) ''
        (region D p c hc : Set (packet D p c hc).Tensor)) =
      ((p : ENNReal) ^ Module.finrank ℚ_[p] (packet D p c hc).Tensor)⁻¹ *
        (regionIndex D p c hc : ENNReal)⁻¹ := by
  rw [region_haar_image_smul_padic, region_normalizedHaar_eq_inv_index]

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
