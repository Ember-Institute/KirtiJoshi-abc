import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWitnessHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogBall

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-EQUAL-NORM-HULL
source: scalar integral balls and the actual normalization span; Joshi III
principal hull (3568--3574).
fidelity: equal factor norms imply equal scalar lattices and equal scalar
normalization regions, without equating the scalar elements themselves.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance equalNormIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem scalarLattice_eq_of_norm_eq (z w : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) (hw : ∀ i, w i ≠ 0) (hn : ∀ i, ‖z i‖ = ‖w i‖) :
    P.scalarLattice z = P.scalarLattice w := by
  unfold scalarLattice
  congr 1
  funext i
  rw [LocalPadicLog.mul_image_closedBall _ (hz i),
    LocalPadicLog.mul_image_closedBall _ (hw i), hn i]

theorem scalarNormalization_eq_of_norm_eq (z w : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) (hw : ∀ i, w i ≠ 0) (hn : ∀ i, ‖z i‖ = ‖w i‖) :
    (P.scalarNormalization z hz : Set P.Tensor) = (P.scalarNormalization w hw : Set P.Tensor) := by
  have heq (a : ∀ i, P.Factor i) (ha : ∀ i, a i ≠ 0) :
      (P.normalizationHull (P.scalarLattice a) : Set P.Tensor) = P.scalarNormalization a ha :=
    (P.normalizationHull_eq_leastHull _ (P.scalarLattice_isCompact_of_nonzero a ha).isBounded
      (P.scalarLattice_normalizationHaar_pos a ha)).trans (P.leastHull_scalarLattice a ha)
  rw [← heq z hz, ← heq w hw, P.scalarLattice_eq_of_norm_eq z w hz hw hn]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
