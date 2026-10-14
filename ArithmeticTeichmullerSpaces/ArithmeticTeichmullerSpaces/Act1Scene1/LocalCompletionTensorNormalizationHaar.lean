import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationCompact
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-HAAR
source: actual compact open Z_p integral closure and Haar uniqueness;
reference maximal-order normalization as an API guide.
fidelity: constructs actual Haar measure normalized at the integral closure
and computes its scalar relation to the earlier unit-lattice normalization.
No equality of the two integral structures, hull or paper theta-volume
identification is assumed. Original proof; no reference code is copied here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory TopologicalSpace
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

def normalizationCompact : PositiveCompacts P.Tensor where
  carrier := P.normalization
  isCompact' := P.normalization_isCompact
  interior_nonempty' := by
    rw [P.normalization_isOpen.interior_eq]
    exact ⟨0, P.normalization.zero_mem⟩

def normalizationHaar : Measure P.Tensor := Measure.addHaarMeasure P.normalizationCompact
instance normalizationHaar_isAddHaarMeasure : P.normalizationHaar.IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure P.normalizationCompact).IsAddHaarMeasure
instance normalizationHaar_regular : P.normalizationHaar.Regular :=
  inferInstanceAs (Measure.addHaarMeasure P.normalizationCompact).Regular

theorem normalizationHaar_normalization : P.normalizationHaar P.normalization = 1 :=
  Measure.addHaarMeasure_self

def normalizationMass : ENNReal := P.normalizedHaar P.normalization

theorem one_le_normalizationMass : 1 ≤ P.normalizationMass := by
  rw [← P.normalizedHaar_unitLattice]
  exact measure_mono P.unitLattice_le_normalization

theorem normalizationMass_lt_top : P.normalizationMass < ⊤ :=
  P.normalization_isCompact.measure_lt_top

theorem normalizedHaar_eq_normalizationMass_mul (S : Set P.Tensor) :
    P.normalizedHaar S = P.normalizationMass * P.normalizationHaar S := by
  let c := Measure.addHaarScalarFactor P.normalizedHaar P.normalizationHaar
  have h : P.normalizedHaar = c • P.normalizationHaar :=
    Measure.isAddLeftInvariant_eq_smul_of_regular P.normalizedHaar P.normalizationHaar
  have hmass : P.normalizationMass = (c : ENNReal) := by
    rw [normalizationMass, h, Measure.smul_apply, P.normalizationHaar_normalization]
    change (c : ENNReal) * 1 = _
    rw [mul_one]
  calc
    P.normalizedHaar S = c • P.normalizationHaar S := by rw [h, Measure.smul_apply]
    _ = (c : ENNReal) * P.normalizationHaar S := rfl
    _ = _ := by rw [hmass]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
