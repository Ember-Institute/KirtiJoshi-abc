import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndeterminacyRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWeightedRegionVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-LOG-VOLUME
source: actual normalization Haar, scalar determinant and general completion
norm formulas; Joshi III `le:volume-lemma3` (containment and volume).
fidelity: normalized real log-volume, its exact scalar-normalization formula,
and monotonicity into the actual factor-automorphism orbit. All applications
use positive finite Haar regions. Original proofs; no reference code copied.
boundary: Scene1/Derived; no paper theta or BK identification.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open JoshiTeich.Prologue MeasureTheory
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance logFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance logIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def normalizationLogVolume (S : Set P.Tensor) : ℝ :=
  Real.log (P.normalizationHaar S).toReal / (Module.finrank ℚ_[p] P.Tensor : ℝ)

theorem normalizationLogVolume_scalarNormalization (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) :
    P.normalizationLogVolume (P.scalarNormalization z hz) =
      ∑ i, Real.log ‖z i‖ / (Arithmetic.localDeg (P.place i) : ℝ) := by
  unfold normalizationLogVolume
  rw [P.normalizationHaar_scalarNormalization_eq_det_norm,
    ← P.normalizedHaar_scalarLattice_eq_det_norm]
  exact P.degreeLogVolume_scalarLattice_eq_norm_sum_general z hz

theorem normalizationLogVolume_mono {U V : Set P.Tensor} (hUV : U ⊆ V)
    (hpos : 0 < P.normalizationHaar U) (hfin : P.normalizationHaar V ≠ ⊤) :
    P.normalizationLogVolume U ≤ P.normalizationLogVolume V := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.log_le_log
  · exact ENNReal.toReal_pos hpos.ne' (ne_top_of_le_ne_top hfin (measure_mono hUV))
  · exact ENNReal.toReal_mono hfin (measure_mono hUV)

theorem normalizationLogVolume_scalarNormalization_le_factorOrbit
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.normalizationLogVolume (P.scalarNormalization z hz) ≤
      P.normalizationLogVolume (P.factorOrbitScalarRegion z hz) :=
  P.normalizationLogVolume_mono (P.scalarNormalization_subset_factorOrbitScalarRegion z hz)
    ((P.scalarLattice_normalizationHaar_pos z hz).trans_le
      (measure_mono (P.scalarLattice_le_scalarNormalization z hz)))
    (P.factorOrbitScalarRegion_haar_pos_lt_top z hz).2.ne

theorem normalizationLogVolume_pure_principalRegion (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) :
    P.normalizationLogVolume (P.principalRegion (P.pure z)) =
      ∑ i, Real.log ‖z i‖ / (Arithmetic.localDeg (P.place i) : ℝ) := by
  rw [← P.scalarNormalization_eq_principalRegion z hz]
  exact P.normalizationLogVolume_scalarNormalization z hz

theorem normalizationLogVolume_principalRegion_le_factorOrbit
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.normalizationLogVolume (P.principalRegion (P.pure z)) ≤
      P.normalizationLogVolume (P.factorOrbitScalarRegion z hz) := by
  rw [← P.scalarNormalization_eq_principalRegion z hz]
  exact P.normalizationLogVolume_scalarNormalization_le_factorOrbit z hz

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
