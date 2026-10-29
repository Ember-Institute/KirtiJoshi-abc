import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionBaseWeightedDefect

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-BASE-WEIGHTED-PRODUCT-DEFECT
source: the strict actual weighted log defect, positivity of corrected paper
root norms, and finite-product logarithm/rpow laws.
fidelity: converts the actual weighted-carrier strict log inequality into a
strict product inequality. The product remains indexed by actual torsion and
base carriers; no paper representative or theta-volume identity is inferred.
boundary: Scene1/Derived. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def iutInitialThetaTorsionWeightedPaperRootProduct : ℝ :=
  ∏ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
    actualPaperRootNorm D s ^ Arithmetic.qPilotWeight s.1

def iutInitialThetaTorsionBaseSectionPaperRootProduct : ℝ :=
  ∏ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
    actualPaperRootNorm D (iutInitialThetaTorsionBaseSection D b)

theorem iutInitialThetaTorsionWeightedPaperRootProduct_pos :
    0 < iutInitialThetaTorsionWeightedPaperRootProduct D := by
  unfold iutInitialThetaTorsionWeightedPaperRootProduct
  exact Finset.prod_pos fun s _ => Real.rpow_pos_of_pos
    (actualPaperRootNorm_mem_Ioo D s).1 _

theorem iutInitialThetaTorsionBaseSectionPaperRootProduct_pos :
    0 < iutInitialThetaTorsionBaseSectionPaperRootProduct D := by
  unfold iutInitialThetaTorsionBaseSectionPaperRootProduct
  exact Finset.prod_pos fun b _ =>
    (actualPaperRootNorm_mem_Ioo D (iutInitialThetaTorsionBaseSection D b)).1

theorem iutInitialThetaTorsionWeightedPaperRootProduct_negLog_eq_weightedPaperLogSum :
    -Real.log (iutInitialThetaTorsionWeightedPaperRootProduct D) =
      ∑ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        Arithmetic.qPilotWeight s.1 * (-Real.log (actualPaperRootNorm D s)) := by
  unfold iutInitialThetaTorsionWeightedPaperRootProduct
  rw [Real.log_prod (fun s _ =>
      (Real.rpow_pos_of_pos (actualPaperRootNorm_mem_Ioo D s).1 _).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [Real.log_rpow (actualPaperRootNorm_mem_Ioo D s).1]
  ring

theorem iutInitialThetaTorsionBaseSectionPaperRootProduct_negLog_eq_unweightedPaperLogSum :
    -Real.log (iutInitialThetaTorsionBaseSectionPaperRootProduct D) =
      ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        -Real.log (actualPaperRootNorm D
          (iutInitialThetaTorsionBaseSection D b)) := by
  unfold iutInitialThetaTorsionBaseSectionPaperRootProduct
  rw [Real.log_prod (fun b _ =>
      (actualPaperRootNorm_mem_Ioo D
        (iutInitialThetaTorsionBaseSection D b)).1.ne'),
    ← Finset.sum_neg_distrib]

theorem iutInitialThetaTorsionWeightedPaperRootProduct_gt_baseSectionProduct :
    iutInitialThetaTorsionBaseSectionPaperRootProduct D <
      iutInitialThetaTorsionWeightedPaperRootProduct D := by
  have hlog := iutInitialThetaTorsionSource_weightedPaperLogSum_lt_baseSectionUnweightedSum D
  rw [← iutInitialThetaTorsionWeightedPaperRootProduct_negLog_eq_weightedPaperLogSum D,
    ← iutInitialThetaTorsionBaseSectionPaperRootProduct_negLog_eq_unweightedPaperLogSum D] at hlog
  have hlogs : Real.log (iutInitialThetaTorsionBaseSectionPaperRootProduct D) <
      Real.log (iutInitialThetaTorsionWeightedPaperRootProduct D) := by
    linarith
  exact (Real.log_lt_log_iff
    (iutInitialThetaTorsionBaseSectionPaperRootProduct_pos D)
    (iutInitialThetaTorsionWeightedPaperRootProduct_pos D)).mp hlogs

end
end JoshiTeich.Act1Scene1
