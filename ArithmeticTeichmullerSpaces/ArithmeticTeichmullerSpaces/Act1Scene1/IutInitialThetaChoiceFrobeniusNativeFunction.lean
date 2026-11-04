import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLocalizationChoice

/-!
source-id: JT-SCENE1-INITIAL-THETA-CHOICE-FROBENIUS-NATIVE-FUNCTION
source: Joshi II `se:ff-rings`, the original Frobenius on a choice of
contracting Teichmuller localization of the actual integral Witt ring.
fidelity: saves the original choice Frobenius as a function with explicit
original ChoiceRing input and output types. The pointwise identity follows
from its definition. The contracting element and its original hypotheses
remain arbitrary. No independent standard comparison, carrier replacement
or new action is introduced. Original proof; no reference code copied.
boundary: function interface only; naturality, completion and paper B,
period and BK identities remain separate. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice.NativeFunction

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceFrobeniusNativeFunction :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def frobeniusFun (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w s) :
    InitialThetaWittLocalizationChoice.ChoiceRing D w s :=
  InitialThetaWittLocalizationChoice.choiceFrobenius D w s hs0 hs1 x

theorem frobeniusEquiv_eq_frobeniusFun
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w s) :
    InitialThetaWittLocalizationChoice.choiceFrobenius D w s hs0 hs1 x =
      frobeniusFun D w s hs0 hs1 x := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice.NativeFunction
