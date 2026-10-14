import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadPaperRootProductBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadLogGeneratedHull
import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312SourceSignAudit
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-HULL-PAPER-BOUND
source: actual collated hull Haar and representative ramification gap;
Joshi III root product estimate and preceding negative-log sign discussion.
fidelity: transfers the actual VBad hull bound to the unweighted selected
paper root product and signed log sum, using an inequality instead of an
unproved equality. Computes the exact positive gap for the constructed
ordinary-log model. The literal displayed minus-log source reading is not
adopted; source sign, paper carrier and theta volume freeze remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadThetaHullPaper
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance hullPaperPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
local instance hullPaperIntegralModule (v : iutInitialThetaVBadModuliFinset D) :
    Module ℤ_[Arithmetic.residueChar v.1] (VBadThetaCollatedHull.packet D n σ hσ v).Tensor :=
  Module.compHom (VBadThetaCollatedHull.packet D n σ hσ v).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)
variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include hgen hunit in
theorem selectedPaperProduct_pow_lt_volume (hn : 0 < n) :
    actualSelectedPaperRootNormProduct D ^ n < VBadThetaCollatedHull.volume D n σ hσ C :=
  (actualSelectedPaperRootNormProduct_pow_lt_normalizedVBadRootProduct_pow D n hn).trans_le
    (VBadThetaCollatedHull.normalizedRootProduct_pow_le_volume D n σ hσ C hgen hunit)

include hgen hunit in
theorem negAverageAbsLog_volume_gt_neg_selectedPaperSum (hn : 0 < n) :
    -iutInitialThetaSelectedQRootPaperSum D <
      -(1 / (n : ℝ)) * |Real.log (VBadThetaCollatedHull.volume D n σ hσ C)| :=
  (neg_lt_neg (iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D)).trans_le
    (VBadThetaCollatedHull.negAverageAbsLog_volume_ge_referenceLhs D n σ hσ C hgen hunit hn)

include hgen hunit in
theorem negAverageAbsLog_volume_gt_selectedSignedLogSum (hn : 0 < n) :
    actualSelectedPaperSignedLogSum D <
      -(1 / (n : ℝ)) * |Real.log (VBadThetaCollatedHull.volume D n σ hσ C)| := by
  have hs : actualSelectedPaperSignedLogSum D = -iutInitialThetaSelectedQRootPaperSum D := by
    rw [← actualSelectedPaperSignedLogSum_neg_eq_paperSum D, neg_neg]
  rw [hs]
  exact negAverageAbsLog_volume_gt_neg_selectedPaperSum D n σ hσ C hgen hunit hn

theorem logGeneratedVolume_gap_eq (hn : 0 < n) :
    -(1 / (n : ℝ)) * |Real.log (VBadThetaLogCollation.volume D n σ hσ)| -
        actualSelectedPaperSignedLogSum D =
      iutInitialThetaSelectedQRootPaperSum D -
        JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [VBadThetaLogCollation.negAverageAbsLog_volume_eq_referenceLhs D n σ hσ hn,
    ← actualSelectedPaperSignedLogSum_neg_eq_paperSum D]
  ring

theorem logGeneratedVolume_gap_pos (hn : 0 < n) :
    0 < -(1 / (n : ℝ)) * |Real.log (VBadThetaLogCollation.volume D n σ hσ)| -
      actualSelectedPaperSignedLogSum D := by
  rw [logGeneratedVolume_gap_eq D n σ hσ hn]
  exact sub_pos.mpr (iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D)

end
end JoshiTeich.Act1Scene1.VBadThetaHullPaper
