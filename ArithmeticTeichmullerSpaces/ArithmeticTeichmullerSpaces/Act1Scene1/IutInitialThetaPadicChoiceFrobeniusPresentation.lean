import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicChoiceFrobeniusFunctionLaws

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-CHOICE-FROBENIUS-PRESENTATION
source: Joshi II `se:ff-rings`, denominator presentations under the actual
Witt Frobenius on the original choice localization.
fidelity: specializes the generic denominator calculation to the original
choice Frobenius and its proved integral inclusion law. Records existence
of the original denominator presentations. Carriers and maps are retained;
no comparison law is assumed. Original proof; Prologue R5 unchanged.
boundary: original actual-side presentation laws only; standard comparison,
completion and paper B/period/BK remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceFrobeniusPresentation :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def choicePresentationExists :=
  WittFrobeniusPresentation.exists_presentation
    (Arithmetic.residueChar w.1) (contraction D w)

set_option linter.defProp false in
def choiceFrobeniusPresentation :=
  WittFrobeniusPresentation.map_presentation
    (Arithmetic.residueChar w.1) (contraction D w)
    (InitialThetaWittLocalizationChoice.choiceFrobenius D w
      (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)).toRingHom
    (choiceFrobenius_inclusion_witt D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
