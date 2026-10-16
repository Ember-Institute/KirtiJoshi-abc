import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWeightedRegionVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorWeightDescent

/-!
source-id: JT-SCENE1-ACTUAL-SELECTED-WEIGHTED-REGION-VOLUME
source: Joshi III eq:weights (3554--3557), actual selected completion degrees,
and the proved tensor Haar formula for all nonzero scalars.
fidelity: constructs a region function with the inverse relative-degree
raw-norm formula on each fibre of common moduli local degree. Proves that
this common-degree condition is also necessary. This closes the raw-norm
descent question; it does not assert the condition for arbitrary initial
data, or identify the paper norm, theta region or different untilts.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]
local instance regionIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem weightedDegree_eq_moduliDegree (i : Fin (Fintype.card ↥(fiber D p))) :
    (Arithmetic.localDeg ((packet D p).place i) : ℝ) * relativeWeight D p i =
      Arithmetic.localDeg (moduliAt D p i) := by
  rw [relativeWeight_eq_localDeg_ratio]
  change (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) *
    ((Arithmetic.localDeg (moduliAt D p i) : ℝ) / Arithmetic.localDeg (sourceAt D p i).1) = _
  have hd : (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos _).ne'
  field_simp [hd]

theorem weightedRegionVolume_eq_relative_product (d : ℕ)
    (hd : ∀ i : Fin (Fintype.card ↥(fiber D p)), Arithmetic.localDeg (moduliAt D p i) = d)
    (z : ∀ i, (packet D p).Factor i) (hz : ∀ i, z i ≠ 0) :
    (packet D p).weightedRegionVolume d ((packet D p).scalarLattice z) =
      (packet D p).weightedScalarVolume (relativeWeight D p) z := by
  exact (packet D p).weightedRegionVolume_scalarLattice (relativeWeight D p) d
    (fun i => by rw [weightedDegree_eq_moduliDegree, hd i]) z hz

theorem relative_region_volume_exists_iff_common_moduliDegree :
    (∃ V : Submodule ℤ_[p] (packet D p).Tensor → ℝ,
      ∀ (z : ∀ i, (packet D p).Factor i) (hz : ∀ i, z i ≠ 0),
        V ((packet D p).scalarLattice z) =
          (packet D p).weightedScalarVolume (relativeWeight D p) z) ↔
      ∃ d : ℕ, 0 < d ∧
        ∀ i : Fin (Fintype.card ↥(fiber D p)), Arithmetic.localDeg (moduliAt D p i) = d := by
  rw [(packet D p).exists_weighted_region_volume_iff]
  simp only [weightedDegree_eq_moduliDegree]
  constructor
  · rintro ⟨c, hc⟩
    by_cases hι : Nonempty (Fin (Fintype.card ↥(fiber D p)))
    · let i := Classical.choice hι
      refine ⟨Arithmetic.localDeg (moduliAt D p i), Arithmetic.localDeg_pos _, ?_⟩
      intro j
      exact_mod_cast (hc j).trans (hc i).symm
    · exact ⟨1, by decide, fun i => False.elim (hι ⟨i⟩)⟩
  · rintro ⟨d, _, hd⟩
    exact ⟨d, fun i => by rw [hd i]⟩

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
