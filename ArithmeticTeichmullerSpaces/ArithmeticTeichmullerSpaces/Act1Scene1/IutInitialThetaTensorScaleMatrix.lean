import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorIntegralBasis
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScaleMatrix

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-SCALE-MATRIX
fidelity: constructs the actual canonical logarithm scaling matrix,
proves its determinant nonzero and identifies its determinant in the
actual region's rational basis. Numerical determinant norm, Haar/index
evaluation and paper weighted volume remain open.
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

local instance matrixIndexFintype : Fintype (packet D p c hc).BasisIndex :=
  by classical infer_instance

def scaleMatrix : Matrix (packet D p c hc).BasisIndex (packet D p c hc).BasisIndex ℚ_[p] :=
  (packet D p c hc).scaleMatrix (fun i => InitialThetaLogWitness.value D (c i))
    (fun i => InitialThetaLogWitness.value_ne_zero D (c i))

theorem scaleMatrix_det_eq :
    (scaleMatrix D p c hc).det = LinearMap.det (scale D p c hc).toLinearEquiv.toLinearMap :=
  LocalCompletion.Packet.scaleMatrix_det_eq (packet D p c hc) _ _

theorem scaleMatrix_det_ne_zero : (scaleMatrix D p c hc).det ≠ 0 :=
  LocalCompletion.Packet.scaleMatrix_det_ne_zero (packet D p c hc) _ _

/-- The factor matrix and the actual region basis give the same scaling determinant. -/
theorem scaleMatrix_det_eq_regionBasis :
    (scaleMatrix D p c hc).det =
      (LinearMap.toMatrix (regionRationalBasis D p c hc) (regionRationalBasis D p c hc)
        (scale D p c hc).toLinearEquiv.toLinearMap).det := by
  rw [LinearMap.det_toMatrix]
  exact scaleMatrix_det_eq D p c hc

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
