import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalRawHullConsumer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource

/-!
source-id: JT-SCENE1-ACTUAL-HULL-COST-TRANSFER
source: S1.321 signed Haar transfer, S1.322 negative-log cost, and S1.358 raw
degree accounting; Joshi III 3495--3557 and 3634--3645.
fidelity: constructs the finite cost carrier and VolumeTransfer from actual
local Haar costs. Zero costs are omitted to satisfy the existing strict weight
condition; hull costs are already included in each packet, so there is no
additional hull charge. The ordinary-log collation supplies its geometric
certificates. The raw target consumer uses this producer without a supplied
normalization or transfer bound. Theta/period/untilt and paper volume identity
remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ActualHullCostTransfer
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance costTransferPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)

abbrev PositivePacket :=
  {v : iutInitialThetaVBadModuliFinset D // 0 < VBadThetaHullLogCost.localCost D n σ hσ C v}

variable (theta : ThetaPilotData D.F)
variable (route : PositivePacket D n σ hσ C → theta.index)

/-- Each packet carries the cost of its actual collated hull, counted once. -/
def packetHull : PacketHullData theta.index where
  packet := PositivePacket D n σ hσ C
  packetFintype := inferInstance
  packetToPilot := route
  packetWeight v := VBadThetaHullLogCost.localCost D n σ hσ C v.1
  hull := ULift.{u} Empty
  hullFintype := inferInstance
  hullToPacket := isEmptyElim
  hullWeight := isEmptyElim

theorem packetWeight_pos (v : (packetHull D n σ hσ C theta route).packet) :
    0 < (packetHull D n σ hσ C theta route).packetWeight v := v.2

theorem hullWeight_pos (h : (packetHull D n σ hσ C theta route).hull) :
    0 < (packetHull D n σ hσ C theta route).hullWeight h := h.down.elim

variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include hgen hunit in
theorem cost_eq_packetWeightSum :
    letI := (packetHull D n σ hσ C theta route).packetFintype
    VBadThetaHullLogCost.cost D n σ hσ C =
      ∑ v : (packetHull D n σ hσ C theta route).packet,
        (packetHull D n σ hσ C theta route).packetWeight v := by
  letI := (packetHull D n σ hσ C theta route).packetFintype
  rw [VBadThetaHullLogCost.cost_eq_sum_localCosts D n σ hσ C hgen hunit]
  change (∑ v, VBadThetaHullLogCost.localCost D n σ hσ C v) =
    ∑ v : {v // 0 < VBadThetaHullLogCost.localCost D n σ hσ C v},
      VBadThetaHullLogCost.localCost D n σ hσ C v.1
  rw [← Finset.sum_subtype (Finset.univ.filter fun v =>
    0 < VBadThetaHullLogCost.localCost D n σ hσ C v) (by simp)]
  symm
  apply Finset.sum_filter_of_ne
  intro v _ hv
  exact lt_of_le_of_ne (VBadThetaHullLogCost.localCost_nonneg D n σ hσ C hunit v) hv.symm

variable (thetaBase : theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)

/-- `logVolume` uses the cost convention required by `exp (-logVolume)`. -/
def link : AdelicThetaLinkData D.F :=
  AdelicThetaLinkData.ofInitialThetaData D theta thetaBase
    (packetHull D n σ hσ C theta route) heightData ramification
    (VBadThetaHullLogCost.cost D n σ hσ C) n

include hgen hunit in
theorem volumeTransfer :
    VolumeTransfer (link D n σ hσ C theta route thetaBase heightData ramification) := by
  letI := (packetHull D n σ hσ C theta route).packetFintype
  constructor
  change VBadThetaHullLogCost.cost D n σ hσ C =
    (∑ v : (packetHull D n σ hσ C theta route).packet,
      (packetHull D n σ hσ C theta route).packetWeight v) +
    ∑ h : ULift.{u} Empty, (packetHull D n σ hσ C theta route).hullWeight h
  have hempty : (∑ h : ULift.{u} Empty,
      (packetHull D n σ hσ C theta route).hullWeight h) = 0 :=
    Finset.sum_eq_zero fun h _ => h.down.elim
  rw [hempty, add_zero]
  exact cost_eq_packetWeightSum D n σ hσ C theta route hgen hunit

theorem packetCollationHull :
    PacketCollationHull (link D n σ hσ C theta route thetaBase heightData ramification) := by
  constructor
  · intro v
    letI := theta.indexFintype
    change route v ∈ Finset.univ
    exact Finset.mem_univ _
  · intro h
    exact h.down.elim
  · intro v
    exact (packetWeight_pos D n σ hσ C theta route v).ne'
  · intro h
    exact h.down.elim

include hgen hunit in
theorem volume_eq_exp_neg_logVolume :
    VBadThetaCollatedHull.volume D n σ hσ C =
      Real.exp (-(link D n σ hσ C theta route thetaBase heightData ramification).logVolume) :=
  VBadThetaHullLogCost.volume_eq_exp_neg_cost D n σ hσ C hgen hunit

/-- The actual positive-length collation has a nonempty cost carrier. -/
theorem ordinary_positivePacket_nonempty (hn : 0 < n) :
    Nonempty (PositivePacket D n σ hσ (VBadThetaLogCollation.collation D n σ hσ)) := by
  by_contra h
  have hzero (v : iutInitialThetaVBadModuliFinset D) :
      VBadThetaHullLogCost.localCost D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ) v = 0 := by
    apply le_antisymm
      (le_of_not_gt fun hv => h ⟨⟨v, hv⟩⟩)
    exact VBadThetaHullLogCost.localCost_nonneg D n σ hσ
      (VBadThetaLogCollation.collation D n σ hσ)
      (VBadThetaLogCollation.collation_subset_normalization D n σ hσ) v
  have hpos := VBadThetaHullLogCost.ordinary_cost_pos D n σ hσ hn
  rw [VBadThetaHullLogCost.cost_eq_sum_localCosts D n σ hσ
    (VBadThetaLogCollation.collation D n σ hσ)
    (VBadThetaLogCollation.generator_coverage D n σ hσ)
    (VBadThetaLogCollation.collation_subset_normalization D n σ hσ)] at hpos
  simp only [hzero, Finset.sum_const_zero, lt_self_iff_false] at hpos

end
end JoshiTeich.Act1Scene1.ActualHullCostTransfer

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
variable (theta : ThetaPilotData D.F)
variable (route : ActualHullCostTransfer.PositivePacket D n σ hσ
  (VBadThetaLogCollation.collation D n σ hσ) → theta.index)
variable (thetaBase : theta.index) (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (T : Corollary312Data D.F O p)
variable (hlink : T.scene1.data.link = ActualHullCostTransfer.link D n σ hσ
  (VBadThetaLogCollation.collation D n σ hσ) theta route thetaBase heightData ramification)
variable (hvolume : T.thetaVolume = VBadThetaLogCollation.volume D n σ hσ)

include hlink hvolume in
theorem actualCostLink_volumeNormalization : Corollary312VolumeNormalization p T := by
  constructor
  rw [hvolume, hlink]
  exact ActualHullCostTransfer.volume_eq_exp_neg_logVolume D n σ hσ
    (VBadThetaLogCollation.collation D n σ hσ) theta route
    (VBadThetaLogCollation.generator_coverage D n σ hσ)
    (VBadThetaLogCollation.collation_subset_normalization D n σ hσ)
    thetaBase heightData ramification

include hlink hvolume in
theorem actualCostLink_transferLogBound
    (V : Corollary312VolumeData p T) (Q : Corollary312TateQFamily p T V)
    (hEll : T.ell = D.prime.ℓ) (hlength : T.ellStar = n) :
    Corollary312TransferLogBound p T := by
  have hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D := by
    rw [hlink]
    rfl
  exact canonicalRawTarget_transferLogBound_of_actualHullVolume p D T V Q hEll hTate
    n σ hσ (VBadThetaLogCollation.collation D n σ hσ)
    (VBadThetaLogCollation.generator_coverage D n σ hσ)
    (VBadThetaLogCollation.collation_subset_normalization D n σ hσ)
    (actualCostLink_volumeNormalization p D n σ hσ theta route thetaBase heightData
      ramification T hlink hvolume) hlength hvolume

end
end JoshiTeich.Act1Scene1
