import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale
import Mathlib.LinearAlgebra.Determinant

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALE-MATRIX
source: actual completion tensor basis and factor scaling; Mathlib basis
coordinates, tensor congruence and basis-independent determinants.
fidelity: computes every tensor-scale matrix entry as a product of factor
coordinates, identifies its determinant with that of the actual linear
automorphism and proves it nonzero. The determinant's factor-norm formula
and its Haar/index interpretation remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField
open scoped BigOperators TensorProduct

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance matrixFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance matrixFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance matrixIndexFintype : Fintype P.BasisIndex := by classical infer_instance

/-- The actual tensor scaling map in the factor tensor basis. -/
def scaleMatrix (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    Matrix P.BasisIndex P.BasisIndex ℚ_[p] :=
  LinearMap.toMatrix P.tensorBasis P.tensorBasis (P.scale z hz).toLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem scaleMatrix_apply (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (k l : P.BasisIndex) :
    P.scaleMatrix z hz k l =
      ∏ i, (Module.finBasis ℚ_[p] (P.Factor i)).repr
        (z i * Module.finBasis ℚ_[p] (P.Factor i) (l i)) (k i) := by
  rw [scaleMatrix, LinearMap.toMatrix_apply]
  simp only [LinearEquiv.coe_coe, tensorBasis, Basis.piTensorProduct_apply,
    scale, PiTensorProduct.congr_tprod, Basis.piTensorProduct_repr_tprod_apply]
  rfl

theorem scaleMatrix_det_eq (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    (P.scaleMatrix z hz).det = LinearMap.det (P.scale z hz).toLinearMap :=
  LinearMap.det_toMatrix P.tensorBasis (P.scale z hz).toLinearMap

theorem scaleMatrix_det_ne_zero (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    (P.scaleMatrix z hz).det ≠ 0 :=
  (LinearEquiv.isUnit_det (P.scale z hz) P.tensorBasis P.tensorBasis).ne_zero

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
