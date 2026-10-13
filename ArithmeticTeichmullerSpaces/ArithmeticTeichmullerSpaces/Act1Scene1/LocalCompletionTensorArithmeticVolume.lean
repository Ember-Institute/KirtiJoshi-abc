import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorRawVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-ARITHMETIC-VOLUME
source: actual completion finrank/local-degree identity and raw tensor Haar.
fidelity: replaces every other-factor dimension by its actual arithmetic
local degree. This computes raw volume and supplies no paper weighting.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance arithmeticFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance arithmeticIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem factor_finrank_eq_localDeg (i : ι) :
    Module.finrank ℚ_[p] (P.Factor i) = JoshiTeich.Prologue.Arithmetic.localDeg (P.place i) :=
  finrank_padic_eq_localDeg (P.place i) (P.residueChar_eq i)

theorem normalizedHaar_scalarLattice_eq_localDeg_product
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.normalizedHaar (P.scalarLattice z) =
      ENNReal.ofReal (∏ i, ‖z i‖ ^
        FiniteTensorMatrix.otherDimension
          (fun j => JoshiTeich.Prologue.Arithmetic.localDeg (P.place j)) i) := by
  rw [P.normalizedHaar_scalarLattice_eq_completionNorm_product z hz hz1]
  simp only [P.factor_finrank_eq_localDeg]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
