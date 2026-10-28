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
open scoped BigOperators Classical NNReal
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

theorem groupedRegionVolume_logRegions_lt_one
    (hι : Nonempty (Index D p)) :
    groupedRegionVolume D p (logRegions D p) < 1 := by
  rw [groupedRegionVolume_logRegions_eq_relativeRootVolume D p,
    SelectedThetaTensor.relativeRootVolume]
  let g : Index D p → ℝ := fun i =>
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot
        (SelectedThetaTensor.sourceAt D p i)‖ ^ SelectedThetaTensor.relativeWeight D p i
  change (∏ i : Index D p, g i) < 1
  have hpos (i : Index D p) : 0 < g i := by
    dsimp [g]
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)) _
  have hlt (i : Index D p) : g i < 1 := by
    dsimp [g]
    exact Real.rpow_lt_one (norm_nonneg _)
      (iutInitialThetaFullQRoot_norm_lt_one D (SelectedThetaTensor.sourceAt D p i))
      (SelectedThetaTensor.relativeWeight_mem_Ioc D p i).1
  have hprod : ∀ s : Finset (Index D p), s.Nonempty →
      (∀ i ∈ s, 0 < g i) → (∀ i ∈ s, g i < 1) →
      s.prod g < 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      simp at hs
    | @insert a s ha ih =>
      intro hs hposS hltS
      by_cases hs' : s.Nonempty
      · have hrest := ih hs'
          (fun i hi => hposS i (Finset.mem_insert_of_mem hi))
          (fun i hi => hltS i (Finset.mem_insert_of_mem hi))
        rw [Finset.prod_insert ha]
        exact (mul_lt_of_lt_one_right (hposS a (Finset.mem_insert_self _ _)) hrest).trans
          (hltS a (Finset.mem_insert_self _ _))
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hltS a (Finset.mem_insert_self _ _)
  exact hprod Finset.univ ⟨Classical.choice hι, Finset.mem_univ _⟩
    (fun i hi => hpos i) (fun i hi => hlt i)

theorem groupedRegionVolume_logRegions_negLog_pos
    (hι : Nonempty (Index D p)) :
    0 < -Real.log (groupedRegionVolume D p (logRegions D p)) := by
  exact neg_pos.mpr (Real.log_neg (groupedRegionVolume_logRegions_pos D p)
    (groupedRegionVolume_logRegions_lt_one D p hι))

theorem groupedRegionVolume_logRegions_eq_one_iff :
    groupedRegionVolume D p (logRegions D p) = 1 ↔
      ¬ Nonempty (Index D p) := by
  constructor
  · intro hvol
    by_contra hι
    exact (ne_of_lt (groupedRegionVolume_logRegions_lt_one D p hι)) hvol
  · intro hι
    let _ : IsEmpty (Index D p) := ⟨fun i => hι ⟨i⟩⟩
    rw [groupedRegionVolume_logRegions_eq_relativeRootVolume D p,
      SelectedThetaTensor.relativeRootVolume]
    simp

omit [Fact p.Prime] in
theorem selectedIndex_nonempty_iff_sourceAtPrime :
    Nonempty (Index D p) ↔
      ∃ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D ∧
          Arithmetic.residueChar s.1 = p := by
  constructor
  · rintro ⟨i⟩
    exact ⟨SelectedThetaTensor.sourceAt D p i,
      (SelectedThetaTensor.sourceAt_selected_residueChar D p i).1,
      (SelectedThetaTensor.sourceAt_selected_residueChar D p i).2⟩
  · rintro ⟨s, hs, hp⟩
    have hsFiber : s ∈ SelectedThetaTensor.fiber D p := by
      rw [SelectedThetaTensor.fiber, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hs, hp⟩
    let sf : ↥(SelectedThetaTensor.fiber D p) := ⟨s, hsFiber⟩
    exact ⟨(SelectedThetaTensor.enumeration D p).symm sf⟩

theorem groupedRegionVolume_logRegions_eq_one_iff_no_sourceAtPrime :
    groupedRegionVolume D p (logRegions D p) = 1 ↔
      ¬ ∃ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D ∧
          Arithmetic.residueChar s.1 = p := by
  rw [groupedRegionVolume_logRegions_eq_one_iff,
    ← selectedIndex_nonempty_iff_sourceAtPrime D p]

theorem groupedRegionVolume_logRegions_lt_one_iff_sourceAtPrime :
    groupedRegionVolume D p (logRegions D p) < 1 ↔
      ∃ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D ∧
          Arithmetic.residueChar s.1 = p := by
  constructor
  · intro hlt
    by_contra hsource
    have heq := (groupedRegionVolume_logRegions_eq_one_iff_no_sourceAtPrime D p).mpr hsource
    rw [heq] at hlt
    exact (lt_irrefl 1) hlt
  · intro hsource
    exact groupedRegionVolume_logRegions_lt_one D p
      ((selectedIndex_nonempty_iff_sourceAtPrime D p).2 hsource)

theorem groupedRegionVolume_logRegions_negLog_eq_ordp_sum :
    -Real.log (groupedRegionVolume D p (logRegions D p)) =
      ∑ i : Index D p, (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) : ℝ) *
        Arithmetic.ordp (SelectedThetaTensor.sourceAt D p i).1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
            (SelectedThetaTensor.sourceAt D p i)) * Real.log p := by
  rw [groupedRegionVolume_eq_regionVolume D p]
  simpa only [rootVolume] using rootVolume_negLog_eq_ordp_sum D p

theorem groupedRegionVolume_logRegions_eq_exp_neg_ordp_sum :
    groupedRegionVolume D p (logRegions D p) =
      Real.exp (-∑ i : Index D p, (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) : ℝ) *
        Arithmetic.ordp (SelectedThetaTensor.sourceAt D p i).1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
            (SelectedThetaTensor.sourceAt D p i)) * Real.log p) := by
  have hpos := groupedRegionVolume_logRegions_pos D p
  have hlog := groupedRegionVolume_logRegions_negLog_eq_ordp_sum D p
  calc
    groupedRegionVolume D p (logRegions D p) =
        Real.exp (Real.log (groupedRegionVolume D p (logRegions D p))) :=
      (Real.exp_log hpos).symm
    _ = Real.exp (-∑ i : Index D p, (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) : ℝ) *
        Arithmetic.ordp (SelectedThetaTensor.sourceAt D p i).1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
            (SelectedThetaTensor.sourceAt D p i)) * Real.log p) := by
      congr 1
      linarith

theorem groupedRootValue_mem_groupedRegion_with_positive_volume :
    groupedRootValue D p ∈ groupedRegion D p (logRegions D p) ∧
      0 < groupedRegionVolume D p (logRegions D p) := by
  exact ⟨groupedRootValue_mem_groupedRegion D p,
    groupedRegionVolume_logRegions_pos D p⟩

end
end JoshiTeich.Act1Scene1.DegreeBlockGroupedRegionVolume
