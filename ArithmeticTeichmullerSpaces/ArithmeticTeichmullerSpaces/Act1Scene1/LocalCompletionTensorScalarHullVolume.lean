import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorChosenHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarResidueRegion

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALAR-HULL-VOLUME
source: actual scalar tensor lattice, normalization saturation, least
principal hull and Haar determinant; Joshi III le:volume-lemma3.
fidelity: proves the chosen hull of a scalar tensor lattice is exactly its
normalization enlargement, and derives quantitative hull bounds from scalar
lattice containment in any bounded positive-Haar region. No theta identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance scalarHullIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])
variable (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)

theorem scalarNormalization_eq_principalRegion :
    (P.scalarNormalization z hz : Set P.Tensor) = P.principalRegion (P.pure z) := by
  rw [P.scalarNormalization_eq_image]
  change (P.scale z hz) '' (P.normalization : Set P.Tensor) = _
  have h := funext fun x => P.scale_eq_mul_pure z hz x
  rw [h]
  rfl

include hz in
theorem scalarLattice_isCompact_of_nonzero : IsCompact (P.scalarLattice z : Set P.Tensor) := by
  rw [← P.unitLattice_image_scale z hz]
  exact P.unitLatticeCompact.isCompact.image (P.continuousScale z hz).continuous

include hz in
theorem scalarLattice_normalizationHaar_pos : 0 < P.normalizationHaar (P.scalarLattice z) :=
  (P.scalarLattice_isOpen z hz).measure_pos _ ⟨0, Submodule.zero_mem _⟩

theorem scalarNormalization_subset_of_scalarLattice_subset (a : P.Tensor)
    (hregion : (P.scalarLattice z : Set P.Tensor) ⊆ P.principalRegion a) :
    (P.scalarNormalization z hz : Set P.Tensor) ⊆ P.principalRegion a := by
  have hpure : P.pure z ∈ P.scalarLattice z := P.pure_mem_lattice _ z
    (fun i => ⟨1, by simp, mul_one _⟩)
  obtain ⟨b, hb, hab⟩ := hregion hpure
  rintro _ ⟨y, hy, rfl⟩
  change P.scale z hz y ∈ P.principalRegion a
  rw [P.scale_eq_mul_pure, ← hab]
  exact ⟨b * y, P.normalization.mul_mem hb hy, (mul_assoc a b y).symm⟩

theorem leastHull_scalarLattice :
    P.leastHull (P.scalarLattice z) (P.scalarLattice_isCompact_of_nonzero z hz).isBounded
      (P.scalarLattice_normalizationHaar_pos z hz) = P.scalarNormalization z hz := by
  rw [P.scalarNormalization_eq_principalRegion]
  apply P.leastHull_eq_of_principal_minimal _ _ _ (P.pure z) (P.pure_isUnit z hz)
  · rw [← P.scalarNormalization_eq_principalRegion z hz]
    exact P.scalarLattice_le_scalarNormalization z hz
  · intro a _ ha
    rw [← P.scalarNormalization_eq_principalRegion z hz]
    exact P.scalarNormalization_subset_of_scalarLattice_subset z hz a ha

theorem normalizationDegreeVolume_mono {U V : Set P.Tensor}
    (hUV : U ⊆ V) (hV : P.normalizationHaar V ≠ ⊤) :
    P.normalizationDegreeVolume U ≤ P.normalizationDegreeVolume V :=
  Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hV (measure_mono hUV)) (by positivity)

include hz in
theorem degreeVolume_scalarLattice_le_leastHullVolume (U : Set P.Tensor)
    (hU : Bornology.IsBounded U) (hpos : 0 < P.normalizationHaar U)
    (hregion : (P.scalarLattice z : Set P.Tensor) ⊆ U) :
    P.degreeVolume (P.scalarLattice z) ≤ P.normalizationDegreeVolume (P.leastHull U hU hpos) := by
  rw [← P.normalizationDegreeVolume_scalarNormalization_eq_degreeVolume z hz]
  apply P.normalizationDegreeVolume_mono _ (P.leastHull_haar_pos_lt_top U hU hpos).2.ne
  exact P.scalarNormalization_subset_of_scalarLattice_subset z hz _
    (hregion.trans (P.subset_leastHull U hU hpos))

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
