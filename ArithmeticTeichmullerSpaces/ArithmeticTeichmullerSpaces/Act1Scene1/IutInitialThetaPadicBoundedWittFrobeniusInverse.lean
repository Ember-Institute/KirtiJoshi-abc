import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittFrobeniusLaws
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittFrobeniusNativeInverse
import Mathlib.Logic.Function.Conjugate

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-BOUNDED-WITT-FROBENIUS-INVERSE
source: Joshi II `se:ff-rings`, inverse Frobenius on bounded Witt rings.
fidelity: derives inverse commutation from the proved native forward law
and the inverse laws of the original actual and standard equivalences.
The standard inverse law depends only on p and its primality instance.
The original maps, carriers and norm are retained. Original proof.
boundary: bounded inverse commutation only; completion and paper B, period
and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeBoundedFrobeniusInverse :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def ringFun_inverseFrobenius :=
  Function.Semiconj.inverses_right (ringFun_frobenius_native D w)
    (InitialThetaBoundedWittLocalization.NativeFunction.inverseFrobeniusFun_rightInverse D w)
    (PadicWittRhoFrobenius.NativeFunction.inverseFrobeniusFun_leftInverse
      (Arithmetic.residueChar w.1))

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
