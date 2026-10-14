import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarHullVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-HULL-NORMALIZATION-BOUNDS
source: actual least hull, normalization Haar and region monotonicity;
Joshi III log-volume sign discussion (3634--3645).
fidelity: derives positivity and the unit upper bound of actual hull degree
volumes. Upper containment in normalization is geometric input; no theta
or paper norm identity is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

theorem normalizationDegreeVolume_le_one (S : Set P.Tensor) (hS : S ⊆ P.normalization) :
    P.normalizationDegreeVolume S ≤ 1 := by
  have h := P.normalizationDegreeVolume_mono hS
    (show P.normalizationHaar (P.normalization : Set P.Tensor) ≠ ⊤ by
      rw [P.normalizationHaar_normalization]; exact ENNReal.one_ne_top)
  have heq : P.normalizationDegreeVolume (P.normalization : Set P.Tensor) = 1 := by
    rw [normalizationDegreeVolume, P.normalizationHaar_normalization, ENNReal.toReal_one,
      Real.one_rpow]
  exact h.trans_eq heq

theorem leastHull_subset_normalization (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) (hUn : U ⊆ P.normalization) :
    P.leastHull U hU hpos ⊆ P.normalization := by
  have hone : P.principalRegion 1 = (P.normalization : Set P.Tensor) := by
    ext x
    simp [principalRegion]
  rw [← hone]
  exact P.leastHull_le_principalRegion U hU hpos 1 isUnit_one (by rwa [hone])

theorem leastHull_normalizationDegreeVolume_pos (U : Set P.Tensor)
    (hU : Bornology.IsBounded U) (hpos : 0 < P.normalizationHaar U) :
    0 < P.normalizationDegreeVolume (P.leastHull U hU hpos) := by
  apply Real.rpow_pos_of_pos
  exact ENNReal.toReal_pos (P.leastHull_haar_pos_lt_top U hU hpos).1.ne'
    (P.leastHull_haar_pos_lt_top U hU hpos).2.ne

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
