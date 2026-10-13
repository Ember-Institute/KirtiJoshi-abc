import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScaleMatrix
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarDeterminant

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-TENSOR-DET-HAAR
source: actual tensor-scale image, factor determinant formula, and the
proved finite-dimensional p-adic determinant/Haar law.
fidelity: identifies scalar tensor lattice Haar volume with the actual
scaling determinant norm and factor algebraic norms. Keeping the packet
abstract avoids expanding the InitialThetaData construction in this proof.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
open scoped BigOperators Classical

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance detFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance detFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance detBasisIndexFintype : Fintype P.BasisIndex := by infer_instance
local instance detTensorFinite : Module.Finite ℚ_[p] P.Tensor :=
  Module.Finite.of_basis P.tensorBasis
local instance detIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def scaleDet (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) : ℚ_[p] :=
  (P.scaleMatrix z hz).det

theorem normalizedHaar_scalarLattice_eq_det_norm
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.normalizedHaar (P.scalarLattice z) = ENNReal.ofReal ‖P.scaleDet z hz‖ := by
  rw [← P.unitLattice_image_scale z hz]
  change P.normalizedHaar ((P.continuousScale z hz) '' (P.unitLattice : Set P.Tensor)) = _
  rw [PadicHaar.measure_image_linearEquiv_eq_norm_det P.normalizedHaar (P.continuousScale z hz),
    P.normalizedHaar_unitLattice, mul_one]
  exact congrArg (fun x : ℚ_[p] => ENNReal.ofReal ‖x‖) (P.scaleMatrix_det_eq z hz).symm

theorem normalizedHaar_scalarLattice_eq_factorNorm_product
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.normalizedHaar (P.scalarLattice z) =
      ENNReal.ofReal (∏ i, ‖Algebra.norm ℚ_[p] (z i)‖ ^
        FiniteTensorMatrix.otherDimension (fun j => Module.finrank ℚ_[p] (P.Factor j)) i) := by
  rw [P.normalizedHaar_scalarLattice_eq_det_norm z hz, scaleDet,
    P.scaleMatrix_det_eq_factor_norm_prod z hz, norm_prod]
  simp only [norm_pow]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
