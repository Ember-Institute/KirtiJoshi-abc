import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalRawTargetAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualHullCostBridge

/-!
source-id: JT-SCENE1-CANONICAL-RAW-HULL-CONSUMER
source: actual collated-hull Haar estimate and canonical raw degree accounting.
fidelity: derives transfer and volume bounds for the raw completion-norm target
without a preassembled Scene1 accounting field or the impossible unweighted
paper-sum equality. General number-field degree is retained. The actual hull
identity, generator coverage and normalization containment remain explicit;
no paper theta/BK/different-untilt identity is constructed here.
boundary: Scene1/Derived
-/

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
variable (T : Corollary312Data D.F O p) (V : Corollary312VolumeData p T)
variable (Q : Corollary312TateQFamily p T V)
variable (hEll : T.ell = D.prime.ℓ)
variable (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D)
variable (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance rawHullPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)
variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include V Q hEll hTate

private theorem reference_le_rawTarget :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      Corollary312Data.qLogSum p T := by
  rw [canonicalTateQFamily_qLogSum_eq_degree_mul_reference p D Q hEll hTate]
  have hDegree : (1 : ℝ) ≤ Module.finrank ℚ D.F := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Module.finrank_pos : 0 < Module.finrank ℚ D.F))
  exact le_mul_of_one_le_left (iutInitialThetaReferenceAbsLogQ_pos D).le hDegree

include hgen hunit in
theorem canonicalRawTarget_transferLogBound_of_actualHullVolume
    (N : Corollary312VolumeNormalization p T)
    (hlength : T.ellStar = n)
    (hvolume : T.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    Corollary312TransferLogBound p T := by
  have hcost := Corollary312VolumeNormalization.cost_eq_actualHull_cost
    D n σ hσ C p T N hvolume
  have hbound := (neg_le_abs _).trans
    (VBadThetaCollatedHull.absLog_volume_le_mul_referenceAbsLogQ D n σ hσ C hgen hunit)
  have htarget := mul_le_mul_of_nonneg_left
    (reference_le_rawTarget p D T V Q hEll hTate) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  constructor
  have hsum : Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T =
      T.scene1.data.link.logVolume := by
    simpa only [Corollary312PacketWeightSum, Corollary312HullWeightSum] using
      T.scene1.volume_transfer.transferred_volume.symm
  rw [hsum, hlength, hcost]
  exact hbound.trans htarget

omit V Q hEll hTate in
include hgen hunit in
theorem canonicalRawScene1Data_transferLogBound_of_actualHullVolume
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D)
    (hlength : base.target.ellStar = n)
    (hvolume : base.target.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    Corollary312TransferLogBound p base.target := by
  exact canonicalRawTarget_transferLogBound_of_actualHullVolume
    p D base.target base.volume base.qFamily hEll hTate n σ hσ C hgen hunit
    base.normalization hlength hvolume

include hgen hunit in
theorem canonicalRawTarget_thetaVolume_ge_qProduct_of_actualHullVolume
    (N : Corollary312VolumeNormalization p T)
    (hlength : T.ellStar = n)
    (hvolume : T.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor :=
  thetaVolume_lower_bound_of_transfer_log_bound p T V Q.toQFamily N
    (canonicalRawTarget_transferLogBound_of_actualHullVolume
      p D T V Q hEll hTate n σ hσ C hgen hunit N hlength hvolume)

omit V Q hEll hTate in
include hgen hunit in
theorem canonicalRawScene1Data_thetaVolume_ge_qProduct_of_actualHullVolume
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D)
    (hlength : base.target.ellStar = n)
    (hvolume : base.target.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    base.target.thetaVolume ≥
      Corollary312Data.qProduct p base.target base.volume.qFactor := by
  exact canonicalRawTarget_thetaVolume_ge_qProduct_of_actualHullVolume
    p D base.target base.volume base.qFamily hEll hTate n σ hσ C hgen hunit
    base.normalization hlength hvolume

include hgen hunit in
theorem corollary312_of_canonicalRawTateFamily_of_actualHullVolume
    (hn : 0 < n) (hlength : T.ellStar = n)
    (hvolume : T.thetaVolume = VBadThetaCollatedHull.volume D n σ hσ C) :
    Corollary312 p T := by
  have hbound := VBadThetaCollatedHull.negAverageAbsLog_volume_ge_referenceLhs
    D n σ hσ C hgen hunit hn
  have htarget := neg_le_neg (reference_le_rawTarget p D T V Q hEll hTate)
  unfold Corollary312
  rw [hlength, hvolume]
  exact htarget.trans hbound

end
end JoshiTeich.Act1Scene1
