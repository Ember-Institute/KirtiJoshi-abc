import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLocalizationChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.RingEquivFrobeniusConjugationIdentity

/-!
source-id: JT-SCENE1-INITIAL-THETA-CHOICE-FROBENIUS-CONJUGATION
source: Joshi II `se:ff-rings`, Frobenius under a change of contracting
Teichmuller element in the actual bounded Witt localization.
fidelity: specializes the generic full-function conjugation identity to
the original actual choice equivalence and original bounded Frobenius.
The contracting element remains arbitrary with its original nonzero and
norm hypotheses. The complete inferred type retains the original operation
instances. No independent standard coefficient comparison or additional
law is used. Original proof; no reference implementation copied.
boundary: actual-side definition identity only; actual-to-standard
naturality, completion and paper B, period and BK identities remain separate.
Original carriers and Prologue R5 are retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceFrobeniusConjugation :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def choiceFrobenius_function_conjugate
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) :=
  RingEquivFrobeniusConjugationIdentity.conjugate_toFun
    ((choiceEquiv D w s hs0 hs1).toRingEquiv)
    (InitialThetaBoundedWittLocalization.frobeniusEquiv D w)

end
end JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice
