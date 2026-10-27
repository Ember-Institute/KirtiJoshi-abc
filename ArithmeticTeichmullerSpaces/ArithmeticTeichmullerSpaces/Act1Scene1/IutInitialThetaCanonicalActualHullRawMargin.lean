import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullStrictVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullQProductNormalization

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-RAW-MARGIN
source: the canonical raw q-log-sum degree accounting, strict selected-paper
VBad accounting, q-product exponential normalization, and actual-hull lower
bound; Joshi III 1028--1055 and 3617--3645.
fidelity: under the explicit degree-one condition, transports the strict
VBad paper-sum margin to the canonical raw target and then to its q-product
and actual theta-volume.  It does not identify the selected carrier with the
paper locus or remove the degree condition.
boundary: Scene1/Derived; paper representative, H¹ₑ/BK, and global producer
identities remain open.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.RawMargin

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O]
variable (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (theta : ThetaPilotData D.F)
variable (route : CanonicalActualHull.PositivePacket D → theta.index)
variable (thetaBase : theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (X : CanonicalActualHull.AnalyticInput (O := O) p D theta route thetaBase
  heightData ramification)

local instance selectedPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

abbrev Target := CanonicalActualHull.data p D theta route thetaBase heightData ramification X
abbrev Volume := CanonicalActualHull.volumeData p D theta route thetaBase heightData ramification X

theorem qLogSum_lt_vbadPaperSum
    (hDegree : Module.finrank ℚ D.F = 1) :
    Corollary312Data.qLogSum p (Target p D theta route thetaBase heightData ramification X) <
      VBadSelectedPaper.paperSum D := by
  rw [CanonicalActualHull.qLogSum_eq_degree_mul_reference p D theta route thetaBase
    heightData ramification X]
  simpa [hDegree] using VBadSelectedPaper.referenceAbsLogQ_lt_paperSum D

theorem exp_neg_ellStar_mul_vbadPaperSum_lt_qProduct
    (hDegree : Module.finrank ℚ D.F = 1) :
    Real.exp (-((Target p D theta route thetaBase heightData ramification X).ellStar : ℝ) *
        VBadSelectedPaper.paperSum D) <
      Corollary312Data.qProduct p (Target p D theta route thetaBase heightData ramification X)
        (Volume p D theta route thetaBase heightData ramification X).qFactor := by
  rw [CanonicalActualHull.QProductNormalization.qProduct_eq_exp_neg_ellStar_mul_qLogSum
    p D theta route thetaBase heightData ramification X]
  apply Real.exp_lt_exp.mpr
  rw [neg_mul]
  rw [neg_mul]
  apply neg_lt_neg_iff.mpr
  exact mul_lt_mul_of_pos_left
    (qLogSum_lt_vbadPaperSum p D theta route thetaBase heightData ramification X hDegree)
    (by exact_mod_cast (CanonicalActualHull.length_pos D))

theorem exp_neg_ellStar_mul_vbadPaperSum_lt_thetaVolume
    (hDegree : Module.finrank ℚ D.F = 1) :
    Real.exp (-((Target p D theta route thetaBase heightData ramification X).ellStar : ℝ) *
        VBadSelectedPaper.paperSum D) <
      (Target p D theta route thetaBase heightData ramification X).thetaVolume := by
  exact (exp_neg_ellStar_mul_vbadPaperSum_lt_qProduct p D theta route thetaBase
    heightData ramification X hDegree).trans_le
    (CanonicalActualHull.thetaVolume_ge_qProduct p D theta route thetaBase heightData ramification X)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.RawMargin
