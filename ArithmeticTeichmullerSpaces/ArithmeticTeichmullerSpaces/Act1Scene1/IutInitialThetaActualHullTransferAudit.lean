import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadHullLogTransfer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRootProductContracting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadLogGeneratedHull
import ArithmeticTeichmullerSpaces.Act1Scene1.ThetaLogSignAudit

/-!
source-id: JT-SCENE1-INITIAL-THETA-ACTUAL-HULL-TRANSFER-AUDIT
source: actual Haar log volume and Prologue-R5 VolumeTransfer; Joshi III
3495--3557 and 3634--3645 log-volume sign discussion.
fidelity: proves the constructed ordinary-log hull has strictly negative log
volume and cannot supply the current Scene1/VolumeTransfer logVolume field.
This obstruction does not require identifying the base theta norm with a
q-root. Core contracts and old APIs are preserved pending source review.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
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

theorem VBadThetaLogCollation.log_volume_neg (hn : 0 < n) :
    Real.log (VBadThetaLogCollation.volume D n σ hσ) < 0 := by
  apply neg_pos.mp
  rw [VBadThetaLogCollation.negLog_volume_eq_mul_referenceAbsLogQ]
  exact mul_pos (by exact_mod_cast hn) (iutInitialThetaReferenceAbsLogQ_pos D)

theorem Scene1Input.logVolume_ne_log_actualHull
    {K O : Type u} [Field K] [NumberField K] [CommRing O]
    {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (S : Scene1Input K O p) (hn : 0 < n) :
    S.data.link.logVolume ≠ Real.log (VBadThetaLogCollation.volume D n σ hσ) := by
  intro heq
  have hnonneg := S.logVolume_nonneg
  rw [heq] at hnonneg
  exact (not_lt_of_ge hnonneg) (VBadThetaLogCollation.log_volume_neg D n σ hσ hn)

theorem not_VolumeTransfer_of_actualHull_logVolume
    {K : Type u} [Field K] [NumberField K] (L : AdelicThetaLinkData K)
    (hpacket : ∀ i, 0 ≤ L.packetHull.packetWeight i)
    (hhull : ∀ i, 0 ≤ L.packetHull.hullWeight i)
    (heq : L.logVolume = Real.log (VBadThetaLogCollation.volume D n σ hσ)) (hn : 0 < n) :
    ¬ VolumeTransfer L := by
  intro htransfer
  letI := L.packetHull.packetFintype
  letI := L.packetHull.hullFintype
  have hnonneg : 0 ≤ L.logVolume := by
    rw [htransfer.transferred_volume]
    exact add_nonneg (Finset.sum_nonneg fun i _ => hpacket i)
      (Finset.sum_nonneg fun i _ => hhull i)
  rw [heq] at hnonneg
  exact (not_lt_of_ge hnonneg) (VBadThetaLogCollation.log_volume_neg D n σ hσ hn)

end
end JoshiTeich.Act1Scene1
