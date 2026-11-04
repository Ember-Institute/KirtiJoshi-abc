import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusNumeratorNaturality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-NUMERATOR
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on bounded integral Witt numerator presentations.
fidelity: specializes the proved numerator naturality theorem at the
original bounded comparison's integer-ring equivalence. The inferred
result preserves the complete coefficient and Witt instances, the same
mapped function and the original numerator transform formula. No new
comparison premise is introduced. Original proof; no reference
implementation copied. Prologue R5 unchanged.
boundary: numerator naturality only; localization, completion and paper B,
period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusPresentationTransfer

open JoshiTeich.Prologue
open InitialThetaPadicBoundedWittComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusNumerator :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def integerNumeratorNaturality :=
  WittFrobeniusNumeratorNaturality.map_numerator
    (p := Arithmetic.residueChar w.1) (integerEquiv D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusPresentationTransfer
