import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadHullLogTransfer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRootProductContracting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadLogGeneratedHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRepresentativeBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-HULL-NEGATIVE-LOG-COST
source: actual Haar weighted-log transfer and the existing exp(-logVolume)
normalization; Joshi III 3495--3557 and 3634--3645.
fidelity: constructs nonnegative negative-log costs from actual hull Haar,
proves the finite cost transfer, recovers the actual volume by exponentiation,
and derives the selected paper-sum cost upper bound. Signed log measure and
negative-log cost are separate quantities. No Core field or q-root is inverted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadThetaHullLogCost
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
local instance logCostPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)

def localCost (v : iutInitialThetaVBadModuliFinset D) : ℝ :=
  VBadThetaHullLogTransfer.packetLogWeight D n σ hσ v *
    (-VBadThetaHullLogTransfer.packetLogVolume D n σ hσ C v)

def cost : ℝ := -Real.log (VBadThetaCollatedHull.volume D n σ hσ C)

variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include hunit in
theorem localCost_nonneg (v : iutInitialThetaVBadModuliFinset D) :
    0 ≤ localCost D n σ hσ C v :=
  mul_nonneg (VBadThetaHullLogTransfer.packetLogWeight_pos D n σ hσ v).le
    (neg_nonneg.mpr (VBadThetaHullLogTransfer.packetLogVolume_nonpos D n σ hσ C hunit v))

include hgen hunit in
theorem cost_eq_sum_localCosts :
    cost D n σ hσ C = ∑ v : iutInitialThetaVBadModuliFinset D, localCost D n σ hσ C v := by
  unfold cost localCost
  rw [VBadThetaHullLogTransfer.log_volume_eq_weightedPacketLogs D n σ hσ C hgen hunit,
    ← Finset.sum_neg_distrib]
  simp only [mul_neg]

include hgen hunit in
theorem cost_nonneg : 0 ≤ cost D n σ hσ C := by
  rw [cost_eq_sum_localCosts D n σ hσ C hgen hunit]
  exact Finset.sum_nonneg fun v _ => localCost_nonneg D n σ hσ C hunit v

include hgen hunit in
theorem volume_eq_exp_neg_cost :
    VBadThetaCollatedHull.volume D n σ hσ C = Real.exp (-cost D n σ hσ C) := by
  unfold cost
  rw [neg_neg]
  exact (Real.exp_log (VBadThetaCollatedHull.volume_pos D n σ hσ C hgen hunit)).symm

include hgen hunit in
theorem cost_le_mul_selectedPaperSum :
    cost D n σ hσ C ≤ (n : ℝ) * iutInitialThetaSelectedQRootPaperSum D := by
  have h := VBadThetaCollatedHull.absLog_volume_le_mul_referenceAbsLogQ D n σ hσ C hgen hunit
  exact (neg_le_abs _).trans (h.trans (mul_le_mul_of_nonneg_left
    (iutInitialThetaReferenceAbsLogQ_le_selectedPaperSum D) (Nat.cast_nonneg n)))

theorem ordinary_cost_eq_mul_referenceAbsLogQ :
    cost D n σ hσ (VBadThetaLogCollation.collation D n σ hσ) = (n : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) :=
  VBadThetaLogCollation.negLog_volume_eq_mul_referenceAbsLogQ D n σ hσ

theorem ordinary_cost_pos (hn : 0 < n) :
    0 < cost D n σ hσ (VBadThetaLogCollation.collation D n σ hσ) := by
  rw [ordinary_cost_eq_mul_referenceAbsLogQ]
  exact mul_pos (by exact_mod_cast hn) (iutInitialThetaReferenceAbsLogQ_pos D)

end
end JoshiTeich.Act1Scene1.VBadThetaHullLogCost
