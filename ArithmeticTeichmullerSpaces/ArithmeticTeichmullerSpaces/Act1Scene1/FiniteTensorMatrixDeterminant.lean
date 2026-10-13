import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Basic

/-!
source-id: JT-SCENE1-FINITE-TENSOR-MATRIX-DETERMINANT
fidelity: derives the determinant of a finite tensor matrix from the binary
Kronecker determinant formula, including empty tuples and zero dimensions.
The exponent for each factor is the product of all other dimensions.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FiniteTensorMatrix

open scoped BigOperators Matrix Kronecker

noncomputable section
variable {R : Type*} [CommRing R]

local instance productIndexFintype {ι : Type} [Fintype ι] (d : ι → ℕ) :
    Fintype (∀ i, Fin (d i)) := by classical infer_instance

def product {ι : Type} [Fintype ι] (d : ι → ℕ)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) R) :
    Matrix (∀ i, Fin (d i)) (∀ i, Fin (d i)) R :=
  fun k l => ∏ i, A i (k i) (l i)

/-- Product of the dimensions other than the selected factor; no division is used. -/
def otherDimension {ι : Type} [Fintype ι] (d : ι → ℕ) (i : ι) : ℕ := by
  classical
  exact ∏ j, if j = i then 1 else d j

private theorem otherDimension_option_none {ι : Type} [Fintype ι] (d : Option ι → ℕ) :
    otherDimension d none = ∏ j, d (some j) := by
  classical
  simp [otherDimension, Fintype.prod_option]

private theorem otherDimension_option_some {ι : Type} [Fintype ι]
    (d : Option ι → ℕ) (i : ι) :
    otherDimension d (some i) = d none * otherDimension (fun j => d (some j)) i := by
  classical
  simp [otherDimension, Fintype.prod_option]

theorem product_det {ι : Type} [Fintype ι] (d : ι → ℕ)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) R) :
    (product d A).det = ∏ i, (A i).det ^ otherDimension d i := by
  classical
  revert d A
  refine Fintype.induction_empty_option
    (P := fun t _ => ∀ (d : t → ℕ) (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) R),
      (product d A).det = ∏ i, (A i).det ^ otherDimension d i)
    (fun α β _ e ih d A => ?_) (fun d A => ?_) (fun α _ ih d A => ?_) ι
  · letI : Fintype α := Fintype.ofEquiv β e.symm
    let ep := Equiv.piCongrLeft (fun i => Fin (d i)) e
    have hmat : (product d A).submatrix ep ep =
        product (fun i => d (e i)) (fun i => A (e i)) := by
      ext k l
      dsimp [product, Matrix.submatrix]
      rw [← e.prod_comp]
      simp only [ep, Equiv.piCongrLeft_apply_apply]
    have hd (i : α) : otherDimension (fun j => d (e j)) i = otherDimension d (e i) := by
      unfold otherDimension
      rw [← e.prod_comp (fun j => if j = e i then 1 else d j)]
      simp only [e.injective.eq_iff]
    rw [← Matrix.det_submatrix_equiv_self ep (product d A), hmat, ih]
    simp_rw [hd]
    exact e.prod_comp (fun i => (A i).det ^ otherDimension d i)
  · rw [Matrix.det_unique]
    simp [product]
  · let ep : (∀ i, Fin (d i)) ≃
        Fin (d none) × (∀ i : α, Fin (d (some i))) := Equiv.piOptionEquivProd
    have hmat : (product d A).submatrix ep.symm ep.symm =
        (A none) ⊗ₖ (product (fun i => d (some i)) (fun i => A (some i))) := by
      ext k l
      change (∏ i, A i (ep.symm k i) (ep.symm l i)) = _
      rw [Fintype.prod_option]
      rfl
    rw [← Matrix.det_submatrix_equiv_self ep.symm (product d A), hmat,
      Matrix.det_kronecker, ih]
    simp only [Fintype.card_pi, Fintype.card_fin, Fintype.prod_option,
      otherDimension_option_none, otherDimension_option_some]
    rw [← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, Nat.mul_comm]

end
end JoshiTeich.Act1Scene1.FiniteTensorMatrix
