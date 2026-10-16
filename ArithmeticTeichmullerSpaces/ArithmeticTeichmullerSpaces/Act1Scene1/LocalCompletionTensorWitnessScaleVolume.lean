import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWitnessHull

/-!
source-id: JT-SCENE1-TENSOR-WITNESS-SCALE-VOLUME
source: actual normalization Haar, scalar tensor determinant and singleton
normalization hull; Joshi III 3520--3574.
fidelity: computes the degree volume of a pure witness hull and the exact
factor introduced by multiplying each scalar by a contracting element.
boundary: Scene1/Derived; no paper theta or BK volume identity is assumed.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance witnessScaleIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem normalizationDegreeVolume_singleton_pure
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.normalizationDegreeVolume (P.normalizationHull {P.pure z}) =
      ∏ i, ‖z i‖ ^ (1 / (Arithmetic.localDeg (P.place i) : ℝ)) := by
  rw [P.normalizationHull_singleton_eq_principalRegion,
    ← P.scalarNormalization_eq_principalRegion z hz,
    P.normalizationDegreeVolume_scalarNormalization_eq_degreeVolume,
    P.degreeVolume_scalarLattice_eq_norm_product z hz hz1]

theorem normalizationDegreeVolume_singleton_scaled
    (c z : ∀ i, P.Factor i) (hc : ∀ i, c i ≠ 0) (hc1 : ∀ i, ‖c i‖ ≤ 1)
    (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.normalizationDegreeVolume (P.normalizationHull {P.pure (fun i => c i * z i)}) =
      (∏ i, ‖c i‖ ^ (1 / (Arithmetic.localDeg (P.place i) : ℝ))) *
        P.normalizationDegreeVolume (P.normalizationHull {P.pure z}) := by
  rw [P.normalizationDegreeVolume_singleton_pure _ (fun i => mul_ne_zero (hc i) (hz i))
    (fun i => by rw [norm_mul]; exact
      (mul_le_of_le_one_left (norm_nonneg _) (hc1 i)).trans_lt (hz1 i)),
    P.normalizationDegreeVolume_singleton_pure z hz hz1, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
