import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAwayPresentationRelation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-CHOICE-NATIVE-PRESENTATION
source: Joshi II `se:ff-rings`, denominator-power presentations in the
original actual and independent standard bounded Witt localizations.
fidelity: states the existing choice-to-standard presentation law using
the original choice denominator, standard denominator and standard
inclusion explicitly. The comparison and integral Witt functions are the
original saved functions. The proof consumes the original comparison
data's proved presentation law; no new source law, carrier, map or norm
is introduced. Original proof; no reference implementation copied.
boundary: native presentation comparison only; Frobenius commutation,
completion and paper B, period and BK identities remain separate.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceNativePresentation :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def choiceStandardFun_native_presentation
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w (contraction D w))
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w)
    (hx : x * algebraMap _ _
        (InitialThetaWittLocalizationChoice.choiceDenominator D w (contraction D w)) ^ m =
      algebraMap _ _ a) :=
  PadicWittAwayPresentationRelation.of_relation (Arithmetic.residueChar w.1)
    (choiceStandardFun D w x) m (integerWittFun D w a)
    (choiceStandardEquiv_presentation D w x m a hx)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
