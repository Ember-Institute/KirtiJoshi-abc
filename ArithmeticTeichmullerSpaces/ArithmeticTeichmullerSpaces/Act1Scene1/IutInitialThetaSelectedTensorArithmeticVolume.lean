import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorRawVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorArithmeticVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-ARITHMETIC-VOLUME
source: actual selected tensor raw Haar and completion local degrees.
fidelity: computes the actual selected region with arithmetic dimension
exponents. The support remains the full selected prime fibre; paper volume,
theta hull and the final volume transfer remain separate proof obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]
local instance arithmeticIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem region_normalizedHaar_eq_localDeg_product :
    (packet D p).normalizedHaar (region D p) =
      ENNReal.ofReal (∏ i, ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ ^
        FiniteTensorMatrix.otherDimension
          (fun j => Arithmetic.localDeg ((packet D p).place j)) i) := by
  rw [region_normalizedHaar_eq_rootNorm_product]
  simp only [LocalCompletion.Packet.factor_finrank_eq_localDeg]

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
