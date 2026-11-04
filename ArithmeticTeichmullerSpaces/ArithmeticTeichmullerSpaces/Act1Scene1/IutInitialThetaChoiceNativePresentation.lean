import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceFrobeniusNativeFunction
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceFrobeniusGenericComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusPresentation

/-!
source-id: JT-SCENE1-INITIAL-THETA-CHOICE-NATIVE-PRESENTATION
source: Joshi II `se:ff-rings`, denominator-power presentations and
Frobenius on the original actual choice of bounded Witt localization.
fidelity: fixes the presentation relation on the literal original
ChoiceRing type, proves coverage by its original Away presentation, and
applies the proved Witt Frobenius presentation law to the saved native
choice Frobenius function. The element and its original hypotheses remain
arbitrary; no standard comparison, replacement carrier or new action is
introduced. Original proofs; no reference implementation copied.
boundary: actual-side algebraic presentations only; comparison naturality,
completion and paper B, period and BK identities remain separate.
Original carriers and Prologue R5 are retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice.NativePresentation

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

def P (s : InitialThetaTiltIntegers.Integers D w)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w s)
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w) : Prop :=
  x * algebraMap (InitialThetaTiltFontaine.Ainf D w)
      (InitialThetaWittLocalizationChoice.ChoiceRing D w s)
      (InitialThetaWittLocalizationChoice.choiceDenominator D w s) ^ m =
    algebraMap (InitialThetaTiltFontaine.Ainf D w)
      (InitialThetaWittLocalizationChoice.ChoiceRing D w s) a

theorem exists_presentation (s : InitialThetaTiltIntegers.Integers D w)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w s) :
    ∃ (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w), P D w s x m a :=
  IsLocalization.Away.surj
    (InitialThetaWittLocalizationChoice.choiceDenominator D w s) x

theorem nativeFrobenius_presentation
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1)
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w s)
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w)
    (hx : P D w s x m a) :
    P D w s
      (InitialThetaWittLocalizationChoice.NativeFunction.frobeniusFun D w s hs0 hs1 x)
      (Arithmetic.residueChar w.1 * m)
      (WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m a) := by
  exact WittFrobeniusPresentation.map_presentation (Arithmetic.residueChar w.1) s
    (InitialThetaWittLocalizationChoice.choiceFrobenius D w s hs0 hs1).toRingHom
    (InitialThetaWittLocalizationChoice.choiceFrobenius_inclusion_witt D w s hs0 hs1)
    x m a hx

end
end JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice.NativePresentation
