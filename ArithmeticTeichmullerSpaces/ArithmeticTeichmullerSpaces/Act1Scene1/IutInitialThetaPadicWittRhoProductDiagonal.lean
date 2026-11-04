import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoProductEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoCompletionInclusionTarget
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusNativeDiagonal

/-!
source-id: JT-SCENE1-ACTUAL-STANDARD-PADIC-WITT-RHO-PRODUCT-DIAGONAL
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
bounded subring in the product of all rho completions.
fidelity: the existing product comparison agrees with the original bounded
map on the actual diagonal and the native standard diagonal. The latter is
proved equal to the original standard diagonal in a p-only source leaf.
The proof consumes the fixed-radius native formula and retains every radius.
Original proof; Scene1/Derived; closure and paper identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoProductEquiv

open JoshiTeich.Prologue
open InitialThetaPadicWittRhoCompletionComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeProductDiagonal : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem productEquiv_symm_diagonalFun (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (productEquiv D w).symm (InitialThetaWittAllRadiusCompletion.diagonal D w x) =
      PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1)
        (InitialThetaPadicBoundedWittComparison.ringFun D w x) := by
  funext ρ
  rw [productEquiv_symm_apply]
  exact completedRingEquiv_inclusionFun D w ρ x

theorem productEquiv_diagonalFun (x : InitialThetaBoundedWittLocalization.Ring D w) :
    productEquiv D w
        (PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1)
          (InitialThetaPadicBoundedWittComparison.ringFun D w x)) =
      InitialThetaWittAllRadiusCompletion.diagonal D w x := by
  apply (productEquiv D w).symm.injective
  rw [RingEquiv.symm_apply_apply, productEquiv_symm_diagonalFun]

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoProductEquiv
