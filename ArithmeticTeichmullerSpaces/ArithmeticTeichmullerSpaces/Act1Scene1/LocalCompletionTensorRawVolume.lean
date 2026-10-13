import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDetHaar
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraNorm

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-RAW-VOLUME
source: actual scalar algebraic norm/completion norm equality and tensor Haar.
fidelity: evaluates contracting scalar tensor-region raw volume with actual
completion norms and other-factor dimension exponents. Paper weighting remains.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance rawFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) := padicAlgebra (P.residueChar_eq i)
local instance rawFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) := finite_padicAlgebra (P.residueChar_eq i)
local instance rawIntegralModule : Module ℤ_[p] P.Tensor := Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem normalizedHaar_scalarLattice_eq_completionNorm_product
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.normalizedHaar (P.scalarLattice z) =
      ENNReal.ofReal (∏ i, ‖z i‖ ^
        FiniteTensorMatrix.otherDimension (fun j => Module.finrank ℚ_[p] (P.Factor j)) i) := by
  rw [P.normalizedHaar_scalarLattice_eq_factorNorm_product z hz]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [LocalCompletion.norm_algebraNorm_eq_completionNorm_of_contracting
    (P.place i) (P.residueChar_eq i) (z i) (hz i) (hz1 i)]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
