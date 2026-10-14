import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadHullLogCost
import ArithmeticTeichmullerSpaces.Act1Scene1.TransferQLowerBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-ACTUAL-HULL-COST-BRIDGE
source: actual Haar negative-log cost and the existing Scene1 exponential
normalization/finite transfer consumers.
fidelity: proves exp(-link.logVolume) identifies link.logVolume with the
actual negative-log cost when thetaVolume is the actual hull measure. Under
explicit cost, procession-length and selected q-sum identities, constructs
the formerly supplied transfer bound and consumes it to prove a volume lower
bound. These source identities remain obligations; no actual Scene1 model,
theta/Bloch-Kato identity, corrected source sign or target freeze is claimed.
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
local instance costBridgePrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)
variable {K O : Type u} [Field K] [NumberField K] [CommRing O]
variable (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (T : Corollary312Data K O p)

theorem Corollary312VolumeNormalization.cost_eq_actualHull_cost
    (N : Corollary312VolumeNormalization p T)
    (hvolume : T.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    T.scene1.data.link.logVolume = VBadThetaHullLogCost.cost D n σ hσ C := by
  have h : VBadThetaCollatedHull.volume D n σ hσ C =
      Real.exp (-T.scene1.data.link.logVolume) := hvolume.symm.trans N.thetaVolume_eq_exp_neg_logVolume
  have hlog := congrArg Real.log h
  rw [Real.log_exp] at hlog
  unfold VBadThetaHullLogCost.cost
  rw [hlog, neg_neg]

variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include hgen hunit in
theorem volumeNormalization_of_actualHull_cost
    (hcost : T.scene1.data.link.logVolume = VBadThetaHullLogCost.cost D n σ hσ C)
    (hvolume : T.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    Corollary312VolumeNormalization p T := by
  constructor
  rw [hvolume, hcost]
  exact VBadThetaHullLogCost.volume_eq_exp_neg_cost D n σ hσ C hgen hunit

include hgen hunit in
theorem transferLogBound_of_actualHull_cost
    (hlength : T.ellStar = n)
    (hcost : T.scene1.data.link.logVolume = VBadThetaHullLogCost.cost D n σ hσ C)
    (hq : Corollary312Data.qLogSum p T = iutInitialThetaSelectedQRootPaperSum D) :
    Corollary312TransferLogBound p T := by
  constructor
  have hsum : Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T =
      T.scene1.data.link.logVolume := by
    simpa only [Corollary312PacketWeightSum, Corollary312HullWeightSum] using
      T.scene1.volume_transfer.transferred_volume.symm
  rw [hsum, hcost, hlength, hq]
  exact VBadThetaHullLogCost.cost_le_mul_selectedPaperSum D n σ hσ C hgen hunit

include hgen hunit in
theorem thetaVolume_lower_bound_of_actualHull_cost
    (V : Corollary312VolumeData p T) (Q : Corollary312QFamily p T V)
    (N : Corollary312VolumeNormalization p T)
    (hlength : T.ellStar = n)
    (hcost : T.scene1.data.link.logVolume = VBadThetaHullLogCost.cost D n σ hσ C)
    (hq : Corollary312Data.qLogSum p T = iutInitialThetaSelectedQRootPaperSum D) :
    T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor :=
  thetaVolume_lower_bound_of_transfer_log_bound p T V Q N
    (transferLogBound_of_actualHull_cost D n σ hσ C p T hgen hunit hlength hcost hq)

end
end JoshiTeich.Act1Scene1
