import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogReferenceMargin
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeCoefficients

/-!
source-id: JT-SCENE1-ACTUAL-REFERENCE-COEFFICIENT-ORDINARY-WEIGHT
source: actual representative coefficient, inverse relative completion degree,
and local correction cost; Joshi III eq:weights and 3520--3574.
fidelity: computes the exact ratio between the reference q-pilot coefficient
and the ordinary-log volume weight. The ratio is source residue degree divided
by the moduli global degree; it is not assumed to be <=1. This exposes the
remaining reference-margin arithmetic without selecting a sign.
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
local instance coefficientWeightPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem representativeCoefficient_eq_ordinaryWeight_mul_sourceInertDeg_ratio
    (v : iutInitialThetaOddModSupportFinset D) :
    iutInitialThetaRepresentativeCoefficient D v =
      FullSupportPaperWeightedHull.weight D v *
        ((Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) /
          Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) := by
  let s := FullSupportPaperWeightedHull.selected D v
  have hcoef := iutInitialThetaRepresentativeCoefficient_mul_ramIdx_eq_localDeg_div_finrank D v
  have hw := FullSupportPaperWeightedHull.weight_eq_localDeg_ratio D v
  have hs : (Arithmetic.localDeg s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.localDeg_pos s.1).ne'
  have he : (Arithmetic.ramIdx s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.ramIdx_pos s.1).ne'
  have hM : (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  have hi : (Arithmetic.inertDeg s.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.inertDeg_pos s.1).ne'
  have hlocal : Arithmetic.localDeg s.1 = Arithmetic.ramIdx s.1 * Arithmetic.inertDeg s.1 := rfl
  rw [hw]
  dsimp only [s] at hcoef hs he ⊢
  calc
    iutInitialThetaRepresentativeCoefficient D v =
        (iutInitialThetaRepresentativeCoefficient D v * (Arithmetic.ramIdx s.1 : ℝ)) /
          Arithmetic.ramIdx s.1 := by
      apply (eq_div_iff he).2
      ring
    _ = ((Arithmetic.localDeg v.1 : ℝ) /
          Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) /
          Arithmetic.ramIdx s.1 := by rw [hcoef]
    _ = (Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg s.1 *
        ((Arithmetic.inertDeg s.1 : ℝ) /
          Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) := by
      simp only [hlocal, Nat.cast_mul]
      field_simp [hs, he, hM, hi]
      <;> ring

def referenceLocalMargin (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  iutInitialThetaRepresentativeCoefficient D v * selectedPaperTerm D v - correctedLocalCost D v

theorem referenceLocalMargin_eq_weight_gap
    (v : iutInitialThetaOddModSupportFinset D) :
    referenceLocalMargin D v =
      (iutInitialThetaRepresentativeCoefficient D v - FullSupportPaperWeightedHull.weight D v) *
        selectedPaperTerm D v - localCorrectionCost D v := by
  unfold referenceLocalMargin correctedLocalCost
  ring

theorem referenceLocalMargin_eq_sourceInertDeg_gap
    (v : iutInitialThetaOddModSupportFinset D) :
    referenceLocalMargin D v =
      FullSupportPaperWeightedHull.weight D v *
        (((Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) /
          Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) - 1) *
          selectedPaperTerm D v - localCorrectionCost D v := by
  rw [referenceLocalMargin_eq_weight_gap,
    representativeCoefficient_eq_ordinaryWeight_mul_sourceInertDeg_ratio]
  ring

theorem referenceLocalMargin_neg_of_sourceInertDeg_le_moduliDegree
    (v : iutInitialThetaOddModSupportFinset D)
    (hdeg : Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 ≤
      Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    referenceLocalMargin D v < 0 := by
  rw [referenceLocalMargin_eq_sourceInertDeg_gap]
  have hratio : (Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) /
      Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) - 1 ≤ 0 := by
    have hM : (0 : ℝ) < Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) :=
      Arithmetic.finrank_pos
    exact sub_nonpos.mpr ((div_le_one₀ hM).mpr (by exact_mod_cast hdeg))
  have hp : 0 < selectedPaperTerm D v := by
    unfold selectedPaperTerm
    exact neg_pos.mpr (Real.log_neg (actualPaperRootNorm_mem_Ioo D _).1
      (actualPaperRootNorm_mem_Ioo D _).2)
  have hw : 0 < FullSupportPaperWeightedHull.weight D v :=
    (FullSupportPaperWeightedHull.weight_mem_Ioc D v).1
  have hc : 0 < localCorrectionCost D v := localCorrectionCost_pos D v
  have hnonneg : 0 ≤ FullSupportPaperWeightedHull.weight D v * selectedPaperTerm D v :=
    mul_nonneg hw.le hp.le
  have hterm : FullSupportPaperWeightedHull.weight D v *
      (↑(Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1) /
        ↑(Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) - 1) *
      selectedPaperTerm D v ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hw.le hratio) hp.le
  linarith

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
