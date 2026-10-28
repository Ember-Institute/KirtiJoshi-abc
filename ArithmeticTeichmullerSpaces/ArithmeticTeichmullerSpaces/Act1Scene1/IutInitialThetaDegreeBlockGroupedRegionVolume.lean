import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDegreeBlockRegionGrouping

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-BLOCK-GROUPED-REGION-VOLUME
source: Joshi III `ss:weighted-vol`, `eq:weights` (3522--3557), the
actual degree-block region family and its proved weighted completion volumes.
fidelity: exposes the existing block-product volume as the volume attached to
the grouped actual carrier, then reconnects scalar and ordinary-log regions
to the existing relative weighted root formulas.
boundary: Scene1/Derived; no Haar measure on the grouped tensor, paper carrier,
paper theta-volume, or mixed-moduli descent identity is asserted.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.DegreeBlockGroupedRegionVolume

open JoshiTeich.Prologue SelectedDegreeBlockVolume DegreeBlockTensorGrouping
  DegreeBlockRegionGrouping
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]

/-- The product of the actual degree-block weighted volumes attached to a grouped region. -/
def groupedRegionVolume (S : RegionFamily D p) : ℝ :=
  ∏ d : DegreeSupport D p,
    (degreePacket D p d).weightedRegionVolume (d.1 : ℝ) (S d)

theorem groupedRegionVolume_eq_regionVolume (S : RegionFamily D p) :
    groupedRegionVolume D p S = regionVolume D p S :=
  rfl

theorem groupedRegionVolume_scalarRegions
    (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i)
    (hz : ∀ i, z i ≠ 0) :
    groupedRegionVolume D p (scalarRegions D p z) =
      (SelectedThetaTensor.packet D p).weightedScalarVolume
        (SelectedThetaTensor.relativeWeight D p) z := by
  rw [groupedRegionVolume_eq_regionVolume D p]
  exact regionVolume_scalarRegions D p z hz

theorem groupedRegionVolume_logRegions_eq_relativeRootVolume :
    groupedRegionVolume D p (logRegions D p) =
      SelectedThetaTensor.relativeRootVolume D p := by
  rw [groupedRegionVolume_eq_regionVolume D p]
  simpa only [rootVolume] using rootVolume_eq_relativeRootVolume D p

theorem groupedRegionVolume_logRegions_pos :
    0 < groupedRegionVolume D p (logRegions D p) := by
  rw [groupedRegionVolume_eq_regionVolume D p]
  exact rootVolume_pos D p

theorem groupedRegionVolume_logRegions_negLog_eq_ordp_sum :
    -Real.log (groupedRegionVolume D p (logRegions D p)) =
      ∑ i : Index D p, (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) : ℝ) *
        Arithmetic.ordp (SelectedThetaTensor.sourceAt D p i).1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
            (SelectedThetaTensor.sourceAt D p i)) * Real.log p := by
  rw [groupedRegionVolume_eq_regionVolume D p]
  simpa only [rootVolume] using rootVolume_negLog_eq_ordp_sum D p

theorem groupedRootValue_mem_groupedRegion_with_positive_volume :
    groupedRootValue D p ∈ groupedRegion D p (logRegions D p) ∧
      0 < groupedRegionVolume D p (logRegions D p) := by
  exact ⟨groupedRootValue_mem_groupedRegion D p,
    groupedRegionVolume_logRegions_pos D p⟩

end
end JoshiTeich.Act1Scene1.DegreeBlockGroupedRegionVolume
