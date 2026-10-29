import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVossOmittedPrimeMass

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-PRODUCT-DECOMPOSITION
source: the complete actual odd-support product, the VBad selected product,
and the already proved positive omitted paper-log sum.
fidelity: upgrades the actual selected/omitted additive accounting to an
exact product decomposition and a strict omitted-product contraction when
moduli support is missing. The factors remain actual corrected root norms; no
paper `L'` representative or theta-volume identity is inferred.
boundary: Scene1/Derived. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def iutInitialThetaVBadOmittedRootProduct : ℝ :=
  ∏ s ∈ VBadSelectedPaper.fullSelectedFinset D \
      VBadSelectedPaper.selectedFinset D, actualPaperRootNorm D s

theorem iutInitialThetaVBadOmittedRootProduct_pos :
    0 < iutInitialThetaVBadOmittedRootProduct D := by
  unfold iutInitialThetaVBadOmittedRootProduct
  exact Finset.prod_pos fun s hs => (actualPaperRootNorm_mem_Ioo D s).1

theorem iutInitialThetaVBadOmittedRootProduct_negLog_eq_omittedPaperSum :
    -Real.log (iutInitialThetaVBadOmittedRootProduct D) =
      VBadSelectedPaper.omittedPaperSum D := by
  unfold iutInitialThetaVBadOmittedRootProduct
  unfold VBadSelectedPaper.omittedPaperSum
  rw [Real.log_prod (fun s hs => (actualPaperRootNorm_mem_Ioo D s).1.ne'),
    ← Finset.sum_neg_distrib]

theorem actualSelectedPaperRootNormProduct_eq_rootProduct_mul_omittedRootProduct :
    actualSelectedPaperRootNormProduct D =
      VBadSelectedPaper.rootProduct D * iutInitialThetaVBadOmittedRootProduct D := by
  have hfull := actualSelectedPaperRootNormProduct_negLog_eq_paperSum D
  have hsplit := VBadSelectedPaper.fullPaperSum_eq_selected_add_omitted D
  have hroot := VBadSelectedPaper.negLog_rootProduct_eq_paperSum D
  have homit := iutInitialThetaVBadOmittedRootProduct_negLog_eq_omittedPaperSum D
  have hlogs :
      Real.log (actualSelectedPaperRootNormProduct D) =
        Real.log (VBadSelectedPaper.rootProduct D) +
          Real.log (iutInitialThetaVBadOmittedRootProduct D) := by
    rw [← neg_inj]
    rw [neg_add]
    calc
      -Real.log (actualSelectedPaperRootNormProduct D) =
          VBadSelectedPaper.paperSum D + VBadSelectedPaper.omittedPaperSum D := by
        rw [hfull, hsplit]
      _ = -Real.log (VBadSelectedPaper.rootProduct D) +
          -Real.log (iutInitialThetaVBadOmittedRootProduct D) := by
        rw [hroot, homit]
  calc
    actualSelectedPaperRootNormProduct D =
        Real.exp (Real.log (actualSelectedPaperRootNormProduct D)) := by
      symm
      exact Real.exp_log (actualSelectedPaperRootNormProduct_mem_Ioo D).1
    _ = Real.exp (Real.log (VBadSelectedPaper.rootProduct D) +
        Real.log (iutInitialThetaVBadOmittedRootProduct D)) := by rw [hlogs]
    _ = VBadSelectedPaper.rootProduct D *
        iutInitialThetaVBadOmittedRootProduct D := by
      simp only [Real.exp_add,
        Real.exp_log (VBadSelectedPaper.rootProduct_pos D),
        Real.exp_log (iutInitialThetaVBadOmittedRootProduct_pos D)]

theorem iutInitialThetaVBadOmittedRootProduct_lt_one_of_missing
    (hmissing : iutInitialThetaVBadModuliFinset D ≠
      iutInitialThetaOddModSupportFinset D) :
    iutInitialThetaVBadOmittedRootProduct D < 1 := by
  have hsum : 0 < VBadSelectedPaper.omittedPaperSum D := by
    have hnonneg := VBadSelectedPaper.omittedPaperSum_nonneg D
    have hne : VBadSelectedPaper.omittedPaperSum D ≠ 0 := by
      intro hz
      exact hmissing ((VBadSelectedPaper.omittedPaperSum_eq_zero_iff_coverage D).mp hz)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hlogs : Real.log (iutInitialThetaVBadOmittedRootProduct D) < Real.log 1 := by
    rw [Real.log_one]
    linarith [iutInitialThetaVBadOmittedRootProduct_negLog_eq_omittedPaperSum D]
  exact (Real.log_lt_log_iff
    (iutInitialThetaVBadOmittedRootProduct_pos D) zero_lt_one).mp hlogs

theorem actualSelectedPaperRootNormProduct_lt_rootProduct_of_missing
    (hmissing : iutInitialThetaVBadModuliFinset D ≠
      iutInitialThetaOddModSupportFinset D) :
    actualSelectedPaperRootNormProduct D < VBadSelectedPaper.rootProduct D := by
  rw [actualSelectedPaperRootNormProduct_eq_rootProduct_mul_omittedRootProduct D]
  have hlt := iutInitialThetaVBadOmittedRootProduct_lt_one_of_missing D hmissing
  have hpos := VBadSelectedPaper.rootProduct_pos D
  calc
    VBadSelectedPaper.rootProduct D * iutInitialThetaVBadOmittedRootProduct D <
        VBadSelectedPaper.rootProduct D * 1 :=
      mul_lt_mul_of_pos_left hlt hpos
    _ = VBadSelectedPaper.rootProduct D := by ring

end
end JoshiTeich.Act1Scene1
