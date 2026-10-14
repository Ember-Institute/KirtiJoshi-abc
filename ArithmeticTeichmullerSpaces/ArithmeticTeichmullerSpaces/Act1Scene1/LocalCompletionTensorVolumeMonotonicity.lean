import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDegreeVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-VOLUME-MONOTONICITY
source: Joshi III th:moccor-Mochizuki-form2 (3624--3631), passage from
contained tensor regions to volume bounds; Mathlib measure monotonicity.
fidelity: proves monotonicity of actual dimension-normalized tensor Haar
volume for arbitrary regions with finite upper Haar measure. Normalization
uses the actual tensor unit lattice, not a claimed paper maximal order.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance integralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem degreeVolume_nonneg (S : Set P.Tensor) : 0 ≤ P.degreeVolume S :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

theorem degreeVolume_mono {S T : Set P.Tensor}
    (hST : S ⊆ T) (hT : P.normalizedHaar T ≠ ⊤) :
    P.degreeVolume S ≤ P.degreeVolume T := by
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hT (measure_mono hST)) (by positivity)

theorem degreeVolume_unitLattice :
    P.degreeVolume (P.unitLattice : Set P.Tensor) = 1 := by
  rw [degreeVolume, P.normalizedHaar_unitLattice, ENNReal.toReal_one, Real.one_rpow]

theorem degreeVolume_le_one_of_subset_unitLattice (S : Set P.Tensor)
    (hS : S ⊆ P.unitLattice) : P.degreeVolume S ≤ 1 := by
  have hfin : P.normalizedHaar (P.unitLattice : Set P.Tensor) ≠ ⊤ := by
    rw [P.normalizedHaar_unitLattice]
    exact ENNReal.one_ne_top
  exact (P.degreeVolume_mono hS hfin).trans_eq P.degreeVolume_unitLattice

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
