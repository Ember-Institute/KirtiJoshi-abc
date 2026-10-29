import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadPaperRootProductBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-PAPER-REFERENCE-PRODUCT-GAP
source: the actual selected corrected-root product bound and the normalized
actual VBad q-root product's exponential reference identity.
fidelity: transports the strict actual selected-product comparison to an
explicit `exp (-referenceAbsLogQ)` bound. The result remains on the actual
selected carrier and does not identify it with paper `L'`, thetaVolume, or a
paper weighted volume.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem actualSelectedPaperRootNormProduct_lt_exp_neg_referenceAbsLogQ :
    actualSelectedPaperRootNormProduct D <
      Real.exp (-JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) := by
  rw [← iutInitialThetaNormalizedVBadRelativeQRootProduct_eq_exp_neg_referenceAbsLogQ D]
  exact actualSelectedPaperRootNormProduct_lt_normalizedVBadRootProduct D

end
end JoshiTeich.Act1Scene1
