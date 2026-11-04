import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceNativePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicChoiceNativePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusNativePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusNumerator
import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusPresentationTransferNative

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-UNIFIED-NATURALITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, functorial
Frobenius on the original bounded Witt localization presentations.
fidelity: uses the presentation relation on the literal original choice
carrier and the cached relation on the original standard carrier. Both
actions are the saved native functions of the existing Frobenius maps.
The original comparison presentation law and coefficient numerator
naturality discharge the comparison inputs. Coverage, uniqueness and
action laws come from the proved original-side presentation consumers.
All pure transfer premises are discharged; no new map, carrier, norm or
comparison hypothesis is introduced. The inferred result preserves these
same functions. Original proof; no reference implementation copied.
boundary: original choice-to-standard algebraic Frobenius naturality only;
canonical actual-carrier transport, completion and paper B, period and BK
identities remain separate. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusUnifiedNaturality

open JoshiTeich.Prologue
open InitialThetaPadicBoundedWittComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusUnifiedNaturality :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
private def sourceExists :=
  InitialThetaWittLocalizationChoice.NativePresentation.exists_presentation
    D w (contraction D w)

set_option linter.defProp false in
private def sourceAction :=
  InitialThetaWittLocalizationChoice.NativePresentation.nativeFrobenius_presentation
    D w (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)

set_option linter.defProp false in
def choiceNativePresentation
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w (contraction D w))
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w)
    (hx : InitialThetaWittLocalizationChoice.NativePresentation.P
      D w (contraction D w) x m a) :=
  choiceStandardFun_native_presentation D w x m a hx

set_option linter.defProp false in
def choiceFrobeniusNaturality :=
  FrobeniusPresentationTransferNative.commutes
    (sourceExists D w)
    (PadicWittAwayPresentationRelation.unique (Arithmetic.residueChar w.1))
    (choiceNativePresentation D w)
    (sourceAction D w)
    (PadicWittRhoFrobenius.NativePresentation.away_frobenius_presentation
      (Arithmetic.residueChar w.1))
    (InitialThetaPadicWittFrobeniusPresentationTransfer.integerNumeratorNaturality D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusUnifiedNaturality
