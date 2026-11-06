import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicChoiceFrobeniusPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusPresentationTransferNative

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-PRESENTATION-INTERFACE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
comparison through the original bounded Witt presentations.
fidelity: fixes both original presentation relations, the original
choice-to-standard function, both original Frobenius functions and the
original integral Witt function before consuming four explicit laws.
Source coverage and target uniqueness come from the existing native
presentation consumers. No new bundled map, carrier or norm is introduced.
The final concrete consumer must discharge all four laws from these same
original maps. Original proof; no reference implementation copied.
boundary: this interface is a conditional implication, not a completed
comparison. Canonical actual-carrier transport, completion and paper B,
period and BK identities remain separate. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusPresentationInterface

open JoshiTeich.Prologue
open InitialThetaPadicBoundedWittComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusPresentationInterface :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

private def actualPresentation
    (x : InitialThetaWittLocalizationChoice.ChoiceRing D w (contraction D w))
    (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w) : Prop :=
  x * algebraMap _ _
      (InitialThetaWittLocalizationChoice.choiceDenominator D w (contraction D w)) ^ m =
    algebraMap _ _ a

private def standardPresentation
    (y : PadicBoundedWittLocalization.Ring (Arithmetic.residueChar w.1))
    (m : ℕ) (b : PadicBoundedWittLocalization.Ainf (Arithmetic.residueChar w.1)) : Prop :=
  y * PadicBoundedWittLocalization.inclusion (Arithmetic.residueChar w.1)
      (PadicBoundedWittLocalization.denominator (Arithmetic.residueChar w.1)) ^ m =
    PadicBoundedWittLocalization.inclusion (Arithmetic.residueChar w.1) b

theorem presentation_frobenius_transfer
    (hE : ∀ x m a, actualPresentation D w x m a →
      standardPresentation D w (choiceStandardFun D w x) m (integerWittFun D w a))
    (hF : ∀ x m a, actualPresentation D w x m a →
      actualPresentation D w
        (InitialThetaWittLocalizationChoice.choiceFrobenius D w
          (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w) x)
        (Arithmetic.residueChar w.1 * m)
        (WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m a))
    (hG : ∀ y m b, standardPresentation D w y m b →
      standardPresentation D w
        (PadicWittRhoFrobenius.frobeniusEquiv (Arithmetic.residueChar w.1) y)
        (Arithmetic.residueChar w.1 * m)
        (WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m b))
    (he : ∀ m a,
      integerWittFun D w
          (WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m a) =
        WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m
          (integerWittFun D w a)) :
    ∀ x : InitialThetaWittLocalizationChoice.ChoiceRing D w (contraction D w),
      choiceStandardFun D w
          (InitialThetaWittLocalizationChoice.choiceFrobenius D w
            (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w) x) =
        PadicWittRhoFrobenius.frobeniusEquiv (Arithmetic.residueChar w.1)
          (choiceStandardFun D w x) := by
  intro x
  exact FrobeniusPresentationTransferNative.commutes
    (P := actualPresentation D w) (Q := standardPresentation D w)
    (E := choiceStandardFun D w)
    (F := fun z => InitialThetaWittLocalizationChoice.choiceFrobenius D w
      (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w) z)
    (G := fun z => PadicWittRhoFrobenius.frobeniusEquiv (Arithmetic.residueChar w.1) z)
    (f := integerWittFun D w)
    (index := fun m => Arithmetic.residueChar w.1 * m)
    (tA := WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1))
    (tB := WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1))
    (choicePresentationExists D w)
    (PadicWittRhoFrobenius.presentation_unique (Arithmetic.residueChar w.1))
    hE hF hG he x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusPresentationInterface
