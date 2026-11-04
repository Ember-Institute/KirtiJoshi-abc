import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceFrobeniusNativeFunction

/-!
source-id: JT-SCENE1-INITIAL-THETA-CHOICE-NATIVE-CONJUGATION
source: Joshi II `se:ff-rings`, change of contracting Teichmuller
element and the original actual choice Frobenius definition.
fidelity: identifies the native function on the literal original
ChoiceRing with the original canonical Frobenius conjugated by the
original choice algebra equivalence. The inverse function is projected
from AlgEquiv.symm, as in the original bounded comparison composition.
The contracting element remains arbitrary with its original hypotheses.
No map, carrier, instance or source law is replaced. Original proof;
no reference implementation copied. Prologue R5 retained.
boundary: actual-side function identity only; comparison naturality,
completion and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice.NativeFunction

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceNativeConjugation :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem frobeniusFun_eq_conjugate
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) :
    frobeniusFun D w s hs0 hs1 =
      (InitialThetaWittLocalizationChoice.choiceEquiv D w s hs0 hs1).symm.toEquiv.toFun ∘
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).toEquiv.toFun ∘
          (InitialThetaWittLocalizationChoice.choiceEquiv D w s hs0 hs1).toEquiv.toFun := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice.NativeFunction
