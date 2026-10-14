import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct
import Mathlib.Tactic.Linarith

/-!
source-id: JT-SCENE1-COR312-LITERAL-SOURCE-SIGN-AUDIT
source: Joshi III cor:cor312 (3647--3650), preceding sign discussion
(3634--3645) and volume lower bound (3617--3632).
fidelity: audits the displayed minus sign before the sum of logarithms
against actual contracting selected root norms. The literal right-hand side
is positive, while the negative average absolute log is nonpositive.
The existing Corollary312 API uses positive negative-log q terms and is
preserved; it does not thereby prove fidelity to the literal displayed sum.
No paper carrier identity, particular InitialThetaData model, corrected
source reading or final target freeze is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section

theorem negativeAverageAbsLog_nonpos (n : ℕ) (volume : ℝ) :
    -(1 / (n : ℝ)) * |Real.log volume| ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (abs_nonneg _)

theorem corollary312_requires_qLogSum_nonneg
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) (h : Corollary312 p T) :
    0 ≤ Corollary312Data.qLogSum p T := by
  have hnonpos := negativeAverageAbsLog_nonpos T.ellStar T.thetaVolume
  change -Corollary312Data.qLogSum p T ≤ _ at h
  linarith

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def actualSelectedPaperSignedLogSum : ℝ :=
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  ∑ s : S, Real.log (actualPaperRootNorm D s.1)

theorem actualSelectedPaperSignedLogSum_eq_logProduct :
    actualSelectedPaperSignedLogSum D = Real.log (actualSelectedPaperRootNormProduct D) := by
  unfold actualSelectedPaperSignedLogSum actualSelectedPaperRootNormProduct
  exact (Real.log_prod (fun s _ => (actualPaperRootNorm_mem_Ioo D s.1).1.ne')).symm

theorem actualSelectedPaperSignedLogSum_neg_eq_paperSum :
    -actualSelectedPaperSignedLogSum D = iutInitialThetaSelectedQRootPaperSum D := by
  rw [actualSelectedPaperSignedLogSum_eq_logProduct]
  exact actualSelectedPaperRootNormProduct_negLog_eq_paperSum D

theorem actualSelectedPaperSignedLogSum_neg_pos :
    0 < -actualSelectedPaperSignedLogSum D := by
  rw [actualSelectedPaperSignedLogSum_eq_logProduct]
  exact neg_pos.mpr (Real.log_neg (actualSelectedPaperRootNormProduct_mem_Ioo D).1
    (actualSelectedPaperRootNormProduct_mem_Ioo D).2)

theorem actualSelectedPaper_not_literal_cor312_bound (n : ℕ) (volume : ℝ) :
    ¬ (-(1 / (n : ℝ)) * |Real.log volume| ≥ -actualSelectedPaperSignedLogSum D) := by
  have hleft := negativeAverageAbsLog_nonpos n volume
  have hright := actualSelectedPaperSignedLogSum_neg_pos D
  exact not_le.mpr (hleft.trans_lt hright)

theorem actualSelectedPaper_not_corollary312_of_literal_logTerms
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hterms : Corollary312Data.qLogSum p T = actualSelectedPaperSignedLogSum D) :
    ¬ Corollary312 p T := by
  intro h
  have hsum := corollary312_requires_qLogSum_nonneg p T h
  rw [hterms] at hsum
  have hpos := actualSelectedPaperSignedLogSum_neg_pos D
  linarith

end
end JoshiTeich.Act1Scene1
