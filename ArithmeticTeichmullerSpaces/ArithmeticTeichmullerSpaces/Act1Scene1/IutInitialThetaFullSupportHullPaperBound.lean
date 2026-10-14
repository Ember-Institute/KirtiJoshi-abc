import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportLogHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-HULL-PAPER-BOUND
source: actual complete selected carrier and full-support Haar hull;
Joshi III full odd semistable product estimate (3617--3631).
fidelity: proves a strict selected unweighted root product lower bound for
the actual full-support ordinary-log hull and computes the negative-average
gap. It requires no VBad=full-support certificate and no caller-supplied
tuple or collation. This does not identify paper theta or weighted volume.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FullSupportThetaLogHull
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

theorem selectedPaperRootProduct_lt_normalizedFullRootProduct :
    actualSelectedPaperRootNormProduct D < iutInitialThetaNormalizedRelativeQRootProduct D := by
  have h := iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum D
  rw [← iutInitialThetaNormalizedRelativeQRootProduct_negLog_eq_fullBaseSum D,
    ← actualSelectedPaperRootNormProduct_negLog_eq_paperSum D] at h
  exact (Real.log_lt_log_iff (actualSelectedPaperRootNormProduct_mem_Ioo D).1
    (Real.rpow_pos_of_pos (iutInitialThetaRelativeQRootProduct_pos D) _)).mp (neg_lt_neg_iff.mp h)

theorem selectedPaperRootProduct_pow_lt_volume (hn : 0 < n) :
    actualSelectedPaperRootNormProduct D ^ n < volume D n := by
  rw [volume_eq_normalizedFullRootProduct_pow]
  exact pow_lt_pow_left₀ (selectedPaperRootProduct_lt_normalizedFullRootProduct D)
    (actualSelectedPaperRootNormProduct_mem_Ioo D).1.le hn.ne'

theorem negAverageAbsLog_volume_eq_neg_fullBaseSum (hn : 0 < n) :
    -(1 / (n : ℝ)) * |Real.log (volume D n)| = -iutInitialThetaFullBaseQPilotLogSum D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [absLog_volume_eq_mul_fullBaseSum, neg_mul, ← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]

theorem negAverageAbsLog_volume_gt_neg_fullSelectedPaperSum (hn : 0 < n) :
    -iutInitialThetaSelectedQRootPaperSum D < -(1 / (n : ℝ)) * |Real.log (volume D n)| := by
  rw [negAverageAbsLog_volume_eq_neg_fullBaseSum D n hn]
  exact neg_lt_neg (iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum D)

end
end JoshiTeich.Act1Scene1.FullSupportThetaLogHull
