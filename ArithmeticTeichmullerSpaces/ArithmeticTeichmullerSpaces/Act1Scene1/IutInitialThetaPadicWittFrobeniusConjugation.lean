import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceFrobeniusConjugation
import ArithmeticTeichmullerSpaces.Act1Scene1.EquivFrobeniusConjugation

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-CONJUGATION
source: Joshi II `se:ff-rings`, Frobenius and change of the contracting
Teichmuller element in the original bounded Witt localization.
fidelity: records the original actual choice Frobenius as the conjugate
of the original canonical bounded Frobenius. The general choice identity
is specialized without adding an expected operation-dictionary type.
Only plain functions are compared; the original maps, carriers and
operation instances are retained. No new comparison law is assumed.
Original proofs; no reference implementation copied. Prologue R5 retained.
boundary: definition identities only; Frobenius naturality, completion
and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusConjugation :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def choiceFrobenius_toFun_eq_conjugate :=
  InitialThetaWittLocalizationChoice.choiceFrobenius_function_conjugate D w
    (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
