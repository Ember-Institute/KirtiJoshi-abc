import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDegreeVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-VOLUME-POWER
source: actual dimension-normalized tensor Haar and Joshi III eq:weights
(3554--3557), under a common base local degree.
fidelity: raises the actual region volume to a common degree d and computes
the scalar-region exponents d/localDeg. This is a numerical normalization,
not an additive measure or a maximal-order/paper norm identification.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open JoshiTeich.Prologue
open scoped BigOperators
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance powerIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem degreeVolume_scalarLattice_pow_eq_norm_product (d : ℕ)
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.degreeVolume (P.scalarLattice z) ^ d =
      ∏ i, ‖z i‖ ^ ((d : ℝ) / Arithmetic.localDeg (P.place i)) := by
  rw [P.degreeVolume_scalarLattice_eq_norm_product z hz hz1, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
