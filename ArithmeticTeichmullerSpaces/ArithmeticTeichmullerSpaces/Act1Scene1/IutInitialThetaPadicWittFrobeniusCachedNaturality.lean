import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicChoiceFrobeniusPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicChoiceNativePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusCachedPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusNumerator
import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusPresentationTransferNative

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-CACHED-NATURALITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
comparison through the original bounded Witt denominator presentations.
fidelity: composes the proved source presentation coverage, cached target
presentation uniqueness, original comparison presentation law, both
original Frobenius presentation laws and coefficient numerator naturality.
The cached target relation is shared by the comparison and standard
Frobenius laws. The result type is inferred from these exact proofs; no
new target relation or bundled map type is imposed. All premises of the
pure transfer theorem are discharged. Original functions, carriers and
norms are retained. Original proof; no reference implementation copied.
boundary: Frobenius naturality on the original choice localization only;
canonical actual-carrier transport, completion and paper B, period and
BK identities remain separate. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusCachedNaturality

open JoshiTeich.Prologue
open InitialThetaPadicBoundedWittComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusCachedNaturality :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def choiceFrobeniusNaturality :=
  FrobeniusPresentationTransferNative.commutes
    (choicePresentationExists D w)
    (PadicWittAwayPresentationRelation.unique (Arithmetic.residueChar w.1))
    (choiceStandardFun_native_presentation D w)
    (choiceFrobeniusPresentation D w)
    (PadicWittRhoFrobenius.CachedPresentation.away_frobenius_presentation
      (Arithmetic.residueChar w.1))
    (InitialThetaPadicWittFrobeniusPresentationTransfer.integerNumeratorNaturality D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusCachedNaturality
