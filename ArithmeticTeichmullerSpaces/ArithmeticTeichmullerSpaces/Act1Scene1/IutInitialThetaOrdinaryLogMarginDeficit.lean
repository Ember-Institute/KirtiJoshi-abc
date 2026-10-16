import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogGlobalMargin
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadOrdinaryLogAbsorption

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-MARGIN-DEFICIT
source: actual relative degree weights and ordinary-log correction costs;
Joshi III 3520--3574, 3624--3631.
fidelity: every local margin is at least minus its correction cost.
Equal source and moduli local degrees force equality and a strictly
negative margin; such a place lies outside VBad. No actual degree-one
place or negative global margin is constructed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem localArithmeticMargin_ge_neg_correctionCost
    (v : iutInitialThetaOddModSupportFinset D) :
    -localCorrectionCost D v ≤ localArithmeticMargin D v := by
  have ht : 0 ≤ selectedPaperTerm D v := by
    unfold selectedPaperTerm
    exact neg_nonneg.mpr (Real.log_nonpos (actualPaperRootNorm_mem_Ioo D _).1.le
      (actualPaperRootNorm_mem_Ioo D _).2.le)
  have hw := mul_le_mul_of_nonneg_right (FullSupportPaperWeightedHull.weight_mem_Ioc D v).2 ht
  rw [localArithmeticMargin_eq_difference, correctedLocalCost]
  linarith

theorem localArithmeticMargin_eq_neg_correctionCost_of_degree_eq
    (v : iutInitialThetaOddModSupportFinset D)
    (hd : Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 = Arithmetic.localDeg v.1) :
    localArithmeticMargin D v = -localCorrectionCost D v := by
  have hv : (Arithmetic.localDeg v.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.localDeg_pos v.1).ne'
  rw [localArithmeticMargin_eq_difference, correctedLocalCost,
    FullSupportPaperWeightedHull.weight_eq_localDeg_ratio, hd, div_self hv, one_mul]
  ring

theorem localArithmeticMargin_neg_of_degree_eq
    (v : iutInitialThetaOddModSupportFinset D)
    (hd : Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 = Arithmetic.localDeg v.1) :
    localArithmeticMargin D v < 0 := by
  rw [localArithmeticMargin_eq_neg_correctionCost_of_degree_eq D v hd]
  exact neg_neg_of_pos (localCorrectionCost_pos D v)

theorem not_arithmeticAbsorption_of_degree_eq
    (v : iutInitialThetaOddModSupportFinset D)
    (hd : Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 = Arithmetic.localDeg v.1) :
    ¬arithmeticAbsorption D v := by
  intro h
  exact (not_le_of_gt (localArithmeticMargin_neg_of_degree_eq D v hd))
    ((localArithmeticMargin_nonneg_iff D v).mpr h)

theorem not_mem_vbad_of_degree_eq
    (v : iutInitialThetaOddModSupportFinset D)
    (hd : Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 = Arithmetic.localDeg v.1) :
    v.1 ∉ D.VBad := by
  intro hv
  have h := vbad_source_localDeg_ge_ell_mul D v hv
  rw [hd] at h
  have hp := Arithmetic.localDeg_pos v.1
  have hell := D.prime.five_le
  nlinarith

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
