import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceFrobeniusGenericComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-CHOICE-FROBENIUS-FUNCTION-LAWS
source: Joshi II `se:ff-rings`, the original Frobenius on the alternative
presentation of the same actual bounded Witt ring.
fidelity: saves the original choice Frobenius function's unit,
multiplication and Witt inclusion laws, with its original instances.
No new map, carrier or source law is introduced. Original proof;
no reference implementation copied. Prologue R5 unchanged.
boundary: original-side laws only; comparison commutation and completion
remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceFrobeniusFunctionLaws :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def choiceFrobenius_map_one :=
  (InitialThetaWittLocalizationChoice.choiceFrobenius D w
    (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)).map_one

set_option linter.defProp false in
def choiceFrobenius_map_mul :=
  (InitialThetaWittLocalizationChoice.choiceFrobenius D w
    (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)).map_mul

set_option linter.defProp false in
def choiceFrobenius_inclusion_witt :=
  InitialThetaWittLocalizationChoice.choiceFrobenius_inclusion_witt D w
    (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
