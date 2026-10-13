import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperRootHaarBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-PAPER-ROOT-NORM-PRODUCT
source: actual selected root norms, residue-degree corrected Haar balls and
the existing selected paper-ball product.
fidelity: identifies the selected paper product with a product of actual
paper-corrected root norms and transports its paper negative-log accounting.
No theta hull, Bloch--Kato class or paper `L'` carrier is constructed.
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

def actualSelectedPaperRootNormProduct : ℝ :=
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  ∏ s : S, actualPaperRootNorm D s.1

theorem actualSelectedPaperRootNormProduct_eq_selectedPaperBallProduct :
    actualSelectedPaperRootNormProduct D = iutInitialThetaSelectedPaperBallProduct D := by
  unfold actualSelectedPaperRootNormProduct iutInitialThetaSelectedPaperBallProduct
  apply Finset.prod_congr rfl
  intro s hs
  exact actualPaperRootNorm_eq_rootBallHaar_corrected D s.1

theorem actualSelectedPaperRootNormProduct_mem_Ioo :
    actualSelectedPaperRootNormProduct D ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [actualSelectedPaperRootNormProduct_eq_selectedPaperBallProduct]
  exact iutInitialThetaSelectedPaperBallProduct_mem_Ioo D

theorem actualSelectedPaperRootNormProduct_negLog_eq_paperSum :
    -Real.log (actualSelectedPaperRootNormProduct D) =
      iutInitialThetaSelectedQRootPaperSum D := by
  rw [actualSelectedPaperRootNormProduct_eq_selectedPaperBallProduct]
  exact iutInitialThetaSelectedPaperBallProduct_negLog_eq_paperSum D

end
end JoshiTeich.Act1Scene1
