import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHullNormalizationBounds

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SINGLE-WITNESS-HULL
source: Joshi III principal hull (3568--3574) and the single standard-point
log tensor used in th:moccor-Mochizuki-form2 (3624--3631).
fidelity: a pure tensor alone generates its scalar normalization region
over the actual normalization. Thus one witness in a bounded collation
suffices for an open compact positive-Haar hull and a quantitative bound.
No full scalar-generator inclusion is required. This uses normalization
modules; it makes no assertion that a Z_p span has the same property.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance witnessHullIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem normalizationHull_singleton_eq_principalRegion (a : P.Tensor) :
    (P.normalizationHull {a} : Set P.Tensor) = P.principalRegion a := by
  apply Set.Subset.antisymm
  · exact (P.normalizationHull_le_iff _ (P.principalNormalizationModule a)).mpr
      (Set.singleton_subset_iff.mpr ⟨1, P.normalization.one_mem, mul_one a⟩)
  · rintro _ ⟨b, hb, rfl⟩
    have h := (P.normalizationHull {a}).smul_mem (⟨b, hb⟩ : P.normalization)
      (P.subset_normalizationHull {a} (Set.mem_singleton a))
    change b * a ∈ P.normalizationHull {a} at h
    rwa [mul_comm] at h

theorem scalarNormalization_subset_normalizationHull_of_pure_mem
    (U : Set P.Tensor) (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hw : P.pure z ∈ U) :
    (P.scalarNormalization z hz : Set P.Tensor) ⊆ P.normalizationHull U := by
  rw [P.scalarNormalization_eq_principalRegion,
    ← P.normalizationHull_singleton_eq_principalRegion]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr hw)

theorem normalizationHull_isOpen_of_pure_mem
    (U : Set P.Tensor) (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hw : P.pure z ∈ U) : IsOpen (P.normalizationHull U : Set P.Tensor) := by
  have hsub : (P.scalarLattice z : Set P.Tensor) ⊆ P.normalizationHull U := fun _ hx =>
    P.scalarNormalization_subset_normalizationHull_of_pure_mem U z hz hw
      (P.scalarLattice_le_scalarNormalization z hz hx)
  apply AddSubgroup.isOpen_of_mem_nhds (P.normalizationHull U).toAddSubgroup
  exact Filter.mem_of_superset ((P.scalarLattice_isOpen z hz).mem_nhds
    (Submodule.zero_mem _)) hsub

theorem normalizationHull_isCompact_of_pure_mem
    (U : Set P.Tensor) (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hw : P.pure z ∈ U) (hU : U ⊆ P.normalization) :
    IsCompact (P.normalizationHull U : Set P.Tensor) := by
  have hclosed := AddSubgroup.isClosed_of_isOpen (P.normalizationHull U).toAddSubgroup
    (P.normalizationHull_isOpen_of_pure_mem U z hz hw)
  have hbound := P.normalization_isCompact.isBounded.subset
    (P.normalizationHull_subset_normalization U hU)
  exact hclosed.closure_eq ▸ hbound.isCompact_closure

theorem normalizationHull_haar_pos_lt_top_of_pure_mem
    (U : Set P.Tensor) (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hw : P.pure z ∈ U) (hU : U ⊆ P.normalization) :
    0 < P.normalizationHaar (P.normalizationHull U) ∧
      P.normalizationHaar (P.normalizationHull U) < ⊤ :=
  ⟨(P.normalizationHull_isOpen_of_pure_mem U z hz hw).measure_pos _
      ⟨0, Submodule.zero_mem _⟩,
    (P.normalizationHull_isCompact_of_pure_mem U z hz hw hU).measure_lt_top⟩

theorem degreeVolume_le_normalizationHull_of_pure_mem
    (U : Set P.Tensor) (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hw : P.pure z ∈ U) (hU : U ⊆ P.normalization) :
    P.degreeVolume (P.scalarLattice z) ≤ P.normalizationDegreeVolume (P.normalizationHull U) := by
  rw [← P.normalizationDegreeVolume_scalarNormalization_eq_degreeVolume z hz]
  exact P.normalizationDegreeVolume_mono
    (P.scalarNormalization_subset_normalizationHull_of_pure_mem U z hz hw)
    (P.normalizationHull_haar_pos_lt_top_of_pure_mem U z hz hw hU).2.ne

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
