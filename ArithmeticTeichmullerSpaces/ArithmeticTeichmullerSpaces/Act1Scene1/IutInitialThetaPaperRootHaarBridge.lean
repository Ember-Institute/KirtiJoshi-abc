import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperRelativeNormBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperBallProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-PAPER-ROOT-HAAR-BRIDGE
source: actual normalized Haar of root integral balls and the paper
residue-degree correction. The paper corrected root norm is identified with
the actual corrected Haar value, and its negative logarithm is the existing
paper term. No theta hull or Bloch--Kato realization is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem actualPaperRootNorm_eq_rootBallHaar_corrected
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    actualPaperRootNorm D s =
      iutInitialThetaPaperBallVolume D s := by
  unfold actualPaperRootNorm iutInitialThetaPaperBallVolume
  rw [iutInitialThetaQRootIntegralBall_haar_toReal_eq_norm]

theorem actualPaperRootNorm_negLog_eq_paperTerm
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    -Real.log (actualPaperRootNorm D s) =
      ((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)) *
        Real.log (Arithmetic.residueChar s.1) := by
  rw [actualPaperRootNorm_eq_rootBallHaar_corrected]
  exact iutInitialThetaPaperBallVolume_negLog_eq_paperTerm D s

theorem actualPaperRootNorm_mem_Ioo_via_rootBallHaar
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    actualPaperRootNorm D s ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [actualPaperRootNorm_eq_rootBallHaar_corrected]
  exact iutInitialThetaPaperBallVolume_mem_Ioo D s

end
end JoshiTeich.Act1Scene1
