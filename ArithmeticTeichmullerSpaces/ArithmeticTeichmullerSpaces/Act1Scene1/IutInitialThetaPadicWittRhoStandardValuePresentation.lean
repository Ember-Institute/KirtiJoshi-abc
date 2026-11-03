import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoAwayQuotient
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-STANDARD-VALUE-PRESENTATION
source: Joshi II `se:ff-rings`, the weighted value of the standard bounded
Witt localization and the transported Away presentation.
fidelity: specializes the proved standard presentation formula to the
existing choice equivalence and its saved integer Witt map.
Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

open JoshiTeich.Prologue
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeStandardValuePresentation : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def standard_choice_value_presentation
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w
      (InitialThetaPadicBoundedWittComparison.contraction D w))
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w)
    (hx : x * algebraMap _ _
        (InitialThetaWittLocalizationChoice.choiceDenominator D w
          (InitialThetaPadicBoundedWittComparison.contraction D w)) ^ m =
      algebraMap _ _ a) :=
  PadicWittRhoValue.value_eq_awayQuotient (Arithmetic.residueChar w.1) ρ hρ0 hρtop
    (InitialThetaPadicBoundedWittComparison.choiceStandardFun D w x) m
    (InitialThetaPadicBoundedWittComparison.integerWittFun D w a)
    (InitialThetaPadicBoundedWittComparison.choiceStandardEquiv_presentation D w x m a hx)


end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
