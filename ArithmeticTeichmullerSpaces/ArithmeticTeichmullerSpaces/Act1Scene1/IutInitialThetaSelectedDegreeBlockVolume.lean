import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedWeightedRegionVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-DEGREE-BLOCK-VOLUME
source: Joshi III `ss:weighted-vol`, `eq:weights` (3522--3557), the
actual selected prime fiber and the proved common-weighted-degree criterion.
fidelity: partitions the existing prime-fiber indices by their actual
moduli local degree. Each computed block has a numerical Haar-derived
region volume realizing the original relative-degree norm weights. Their
product is a function of the block-region family and recovers the full
weighted scalar product without a common-degree assumption. The ordinary
log-root regions provide an actual consumer and the original q-log formula.
boundary: Scene1/Derived; retains the degree blocks as data. Does not
identify this carrier with the ungraded tensor region, paper weighted
carrier, different-untilt locus or theta-volume. No new source law is input.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.SelectedDegreeBlockVolume

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ)

abbrev Index := Fin (Fintype.card ↥(SelectedThetaTensor.fiber D p))

def degreeSupport : Finset ℕ :=
  Finset.univ.image (fun i : Index D p => Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i))

abbrev DegreeSupport := ↥(degreeSupport D p)

abbrev DegreeFiber (d : DegreeSupport D p) :=
  {i : Index D p // Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) = d.1}

noncomputable instance degreeFiberFintype (d : DegreeSupport D p) :
    Fintype (DegreeFiber D p d) := Fintype.ofFinite _

theorem degreeSupport_pos (d : DegreeSupport D p) : 0 < d.1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp d.2
  rw [← hi]
  exact Arithmetic.localDeg_pos _

noncomputable def indexSigmaEquiv :
    Index D p ≃ Σ d : DegreeSupport D p, DegreeFiber D p d := by
  refine Equiv.ofBijective (fun i =>
    ⟨⟨Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩, ⟨i, rfl⟩⟩) ?_
  constructor
  · intro i j h
    exact congrArg (fun z => z.2.1) h
  · rintro ⟨⟨d, hd⟩, ⟨i, hi⟩⟩
    change Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) = d at hi
    subst d
    exact ⟨i, rfl⟩

theorem indexSigmaEquiv_index (i : Index D p) : (indexSigmaEquiv D p i).2.1 = i := rfl

def degreePacket (d : DegreeSupport D p) :
    LocalCompletion.Packet ↥D.prime.torsionField p (DegreeFiber D p d) :=
  ⟨fun i => (SelectedThetaTensor.packet D p).place i.1,
    fun i => (SelectedThetaTensor.packet D p).residueChar_eq i.1⟩

variable [Fact p.Prime]

local instance blockIntegralModule (d : DegreeSupport D p) :
    Module ℤ_[p] (degreePacket D p d).Tensor :=
  Module.compHom (degreePacket D p d).Tensor (algebraMap ℤ_[p] ℚ_[p])

local instance originalIntegralModule : Module ℤ_[p] (SelectedThetaTensor.packet D p).Tensor :=
  Module.compHom (SelectedThetaTensor.packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

abbrev RegionFamily := ∀ d : DegreeSupport D p,
  Submodule ℤ_[p] (degreePacket D p d).Tensor

def scalarRegions (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i) : RegionFamily D p :=
  fun d => (degreePacket D p d).scalarLattice (fun i => z i.1)

def regionVolume (S : RegionFamily D p) : ℝ :=
  ∏ d : DegreeSupport D p, (degreePacket D p d).weightedRegionVolume (d.1 : ℝ) (S d)

theorem block_weightedDegree (d : DegreeSupport D p) (i : DegreeFiber D p d) :
    (Arithmetic.localDeg ((degreePacket D p d).place i) : ℝ) *
        SelectedThetaTensor.relativeWeight D p i.1 = d.1 := by
  change (Arithmetic.localDeg ((SelectedThetaTensor.packet D p).place i.1) : ℝ) *
    SelectedThetaTensor.relativeWeight D p i.1 = _
  rw [SelectedThetaTensor.weightedDegree_eq_moduliDegree]
  exact_mod_cast i.2

theorem regionVolume_scalarRegions
    (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i) (hz : ∀ i, z i ≠ 0) :
    regionVolume D p (scalarRegions D p z) =
      (SelectedThetaTensor.packet D p).weightedScalarVolume
        (SelectedThetaTensor.relativeWeight D p) z := by
  calc
    _ = ∏ d : DegreeSupport D p, ∏ i : DegreeFiber D p d,
        ‖z i.1‖ ^ SelectedThetaTensor.relativeWeight D p i.1 := by
      apply Finset.prod_congr rfl
      intro d _
      exact (degreePacket D p d).weightedRegionVolume_scalarLattice
        (fun i => SelectedThetaTensor.relativeWeight D p i.1) d.1
        (block_weightedDegree D p d) (fun i => z i.1) (fun i => hz i.1)
    _ = _ := by
      unfold LocalCompletion.Packet.weightedScalarVolume
      rw [← Fintype.prod_sigma'
        (fun (d : DegreeSupport D p) (i : DegreeFiber D p d) =>
          ‖z i.1‖ ^ SelectedThetaTensor.relativeWeight D p i.1)]
      refine Fintype.prod_equiv (indexSigmaEquiv D p).symm _ _ ?_
      intro s
      have hindex : (indexSigmaEquiv D p).symm s = s.2.1 := by
        have h := indexSigmaEquiv_index D p ((indexSigmaEquiv D p).symm s)
        rw [Equiv.apply_symm_apply] at h
        exact h.symm
      rw [hindex]

theorem weightedScalarVolume_eq_of_blockRegions_eq
    (z w : ∀ i, (SelectedThetaTensor.packet D p).Factor i)
    (hz : ∀ i, z i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (h : scalarRegions D p z = scalarRegions D p w) :
    (SelectedThetaTensor.packet D p).weightedScalarVolume (SelectedThetaTensor.relativeWeight D p) z =
      (SelectedThetaTensor.packet D p).weightedScalarVolume (SelectedThetaTensor.relativeWeight D p) w := by
  rw [← regionVolume_scalarRegions D p z hz, ← regionVolume_scalarRegions D p w hw, h]

def logRegions : RegionFamily D p :=
  scalarRegions D p (fun i => iutInitialThetaFullQRootLogValue D (SelectedThetaTensor.sourceAt D p i))

def rootVolume : ℝ := regionVolume D p (logRegions D p)

omit [Fact p.Prime] in
private theorem logValue_ne_zero (i : Index D p) :
    iutInitialThetaFullQRootLogValue D (SelectedThetaTensor.sourceAt D p i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)

theorem rootVolume_eq_relativeRootVolume :
    rootVolume D p = SelectedThetaTensor.relativeRootVolume D p := by
  rw [rootVolume, logRegions, regionVolume_scalarRegions D p _ (logValue_ne_zero D p)]
  unfold LocalCompletion.Packet.weightedScalarVolume SelectedThetaTensor.relativeRootVolume
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun r : ℝ => r ^ SelectedThetaTensor.relativeWeight D p i)
    (iutInitialThetaFullQRootLogValue_norm_eq D (SelectedThetaTensor.sourceAt D p i))

theorem rootVolume_pos : 0 < rootVolume D p := by
  rw [rootVolume_eq_relativeRootVolume, SelectedThetaTensor.relativeRootVolume]
  exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos
    (norm_pos_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)) _)

theorem rootVolume_negLog_eq_ordp_sum :
    -Real.log (rootVolume D p) =
      ∑ i : Index D p, (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) : ℝ) *
        Arithmetic.ordp (SelectedThetaTensor.sourceAt D p i).1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
            (SelectedThetaTensor.sourceAt D p i)) * Real.log p := by
  rw [rootVolume_eq_relativeRootVolume]
  exact SelectedThetaTensor.relativeRootVolume_negLog_eq_ordp_sum D p

theorem ungraded_region_volume_exists_iff_degreeSupport_card_le_one :
    (∃ V : Submodule ℤ_[p] (SelectedThetaTensor.packet D p).Tensor → ℝ,
      ∀ (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i) (_hz : ∀ i, z i ≠ 0),
        V ((SelectedThetaTensor.packet D p).scalarLattice z) =
          (SelectedThetaTensor.packet D p).weightedScalarVolume
            (SelectedThetaTensor.relativeWeight D p) z) ↔
      (degreeSupport D p).card ≤ 1 := by
  rw [SelectedThetaTensor.relative_region_volume_exists_iff_common_moduliDegree D p]
  constructor
  · rintro ⟨d, _, hd⟩
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact (hd i).trans (hd j).symm
  · intro hcard
    by_cases hι : Nonempty (Index D p)
    · obtain ⟨i⟩ := hι
      refine ⟨Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i),
        Arithmetic.localDeg_pos _, ?_⟩
      intro j
      exact Finset.card_le_one.mp hcard _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · exact ⟨1, by decide, fun i => (hι ⟨i⟩).elim⟩

end
end JoshiTeich.Act1Scene1.SelectedDegreeBlockVolume
