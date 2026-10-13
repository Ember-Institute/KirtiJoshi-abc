import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale
import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteTensorMatrixDeterminant
import Mathlib.RingTheory.Norm.Defs

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALE-MATRIX
source: actual completion tensor basis and factor scaling; Mathlib basis
coordinates, tensor congruence and basis-independent determinants.
fidelity: computes every tensor-scale matrix entry as a product of factor
coordinates and its determinant as a product of factor algebraic norms,
with each exponent equal to the product of the other factor dimensions.
The determinant is nonzero for nonzero scalars. Its absolute-norm and
Haar/index interpretations remain open.
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

/-- Multiplication by one actual local scalar in the finite basis of its completion. -/
def factorMulMatrix (i : ι) (x : P.Factor i) :
    Matrix (Fin (Module.finrank ℚ_[p] (P.Factor i)))
      (Fin (Module.finrank ℚ_[p] (P.Factor i))) ℚ_[p] :=
  Algebra.leftMulMatrix (Module.finBasis ℚ_[p] (P.Factor i)) x

theorem factorMulMatrix_apply (i : ι) (x : P.Factor i)
    (k l : Fin (Module.finrank ℚ_[p] (P.Factor i))) :
    P.factorMulMatrix i x k l =
      (Module.finBasis ℚ_[p] (P.Factor i)).repr
        (x * Module.finBasis ℚ_[p] (P.Factor i) l) k :=
  Algebra.leftMulMatrix_eq_repr_mul (Module.finBasis ℚ_[p] (P.Factor i)) x k l

theorem factorMulMatrix_det_eq_norm (i : ι) (x : P.Factor i) :
    (P.factorMulMatrix i x).det = Algebra.norm ℚ_[p] x :=
  (Algebra.norm_eq_matrix_det (Module.finBasis ℚ_[p] (P.Factor i)) x).symm

theorem factorMulMatrix_det_ne_zero (i : ι) (x : P.Factor i) (hx : x ≠ 0) :
    (P.factorMulMatrix i x).det ≠ 0 := by
  rw [factorMulMatrix_det_eq_norm]
  exact (IsUnit.map (Algebra.norm ℚ_[p]) (isUnit_iff_ne_zero.mpr hx)).ne_zero

theorem factorMulMatrix_det_algebraMap (i : ι) (a : ℚ_[p]) :
    (P.factorMulMatrix i (algebraMap ℚ_[p] (P.Factor i) a)).det =
      a ^ Module.finrank ℚ_[p] (P.Factor i) := by
  rw [factorMulMatrix_det_eq_norm, Algebra.norm_algebraMap]

theorem scaleMatrix_eq_factorMul_prod (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (k l : P.BasisIndex) :
    P.scaleMatrix z hz k l = ∏ i, P.factorMulMatrix i (z i) (k i) (l i) := by
  simp only [scaleMatrix_apply, factorMulMatrix_apply]

theorem scaleMatrix_det_eq_factor_norm_prod (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    (P.scaleMatrix z hz).det =
      ∏ i, Algebra.norm ℚ_[p] (z i) ^
        FiniteTensorMatrix.otherDimension (fun j => Module.finrank ℚ_[p] (P.Factor j)) i := by
  have hmat : P.scaleMatrix z hz =
      FiniteTensorMatrix.product (fun i => Module.finrank ℚ_[p] (P.Factor i))
        (fun i => P.factorMulMatrix i (z i)) := by
    ext k l
    exact P.scaleMatrix_eq_factorMul_prod z hz k l
  rw [hmat, FiniteTensorMatrix.product_det]
  simp only [factorMulMatrix_det_eq_norm]

theorem scaleMatrix_det_common_algebraMap (a : ℚ_[p]) (ha : a ≠ 0) :
    (P.scaleMatrix (fun i => algebraMap ℚ_[p] (P.Factor i) a)
      (fun i => by
        intro h
        exact ha ((algebraMap ℚ_[p] (P.Factor i)).injective (by simpa using h)))).det =
      a ^ (Fintype.card ι * ∏ i, Module.finrank ℚ_[p] (P.Factor i)) := by
  classical
  rw [P.scaleMatrix_det_eq_factor_norm_prod]
  simp only [Algebra.norm_algebraMap]
  simp_rw [← pow_mul]
  have hpow :
      (∏ i, a ^ (Module.finrank ℚ_[p] (P.Factor i) *
        FiniteTensorMatrix.otherDimension
          (fun j => Module.finrank ℚ_[p] (P.Factor j)) i)) =
        a ^ ∑ i, (Module.finrank ℚ_[p] (P.Factor i) *
          FiniteTensorMatrix.otherDimension
            (fun j => Module.finrank ℚ_[p] (P.Factor j)) i) := by
    simpa using (Finset.prod_pow_eq_pow_sum (s := Finset.univ)
      (f := fun i => Module.finrank ℚ_[p] (P.Factor i) *
        FiniteTensorMatrix.otherDimension
          (fun j => Module.finrank ℚ_[p] (P.Factor j)) i) a)
  rw [hpow]
  congr 1
  have hprod (i : ι) :
      Module.finrank ℚ_[p] (P.Factor i) *
          FiniteTensorMatrix.otherDimension
            (fun j => Module.finrank ℚ_[p] (P.Factor j)) i =
        ∏ j, Module.finrank ℚ_[p] (P.Factor j) := by
    unfold FiniteTensorMatrix.otherDimension
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [if_pos rfl, one_mul]
    have herase :
        (∏ x ∈ Finset.univ.erase i,
          if x = i then 1 else (fun j => Module.finrank ℚ_[p] (P.Factor j)) x) =
          ∏ x ∈ Finset.univ.erase i, Module.finrank ℚ_[p] (P.Factor x) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.mem_erase.mp hj |>.1]
    rw [herase]
    simp only [ite_true, one_mul]
    simpa using
      (Finset.mul_prod_erase Finset.univ
        (fun j => Module.finrank ℚ_[p] (P.Factor j))
        (a := i) (Finset.mem_univ i))
  have hsum :
      (∑ i, Module.finrank ℚ_[p] (P.Factor i) *
        FiniteTensorMatrix.otherDimension
          (fun j => Module.finrank ℚ_[p] (P.Factor j)) i) =
        ∑ _i : ι, ∏ j, Module.finrank ℚ_[p] (P.Factor j) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hprod i
  rw [hsum]
  simp [nsmul_eq_mul]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
