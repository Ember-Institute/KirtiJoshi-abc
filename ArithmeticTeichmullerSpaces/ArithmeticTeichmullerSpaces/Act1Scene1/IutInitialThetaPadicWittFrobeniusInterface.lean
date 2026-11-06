import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalizationFrobeniusNaturality

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-INTERFACE
source: Joshi II `se:ff-rings`, localization functoriality.
fidelity: fixes the original integral inclusions and localization in the
proved generic naturality implication. Remaining map and law binders are
explicit; this partial specialization is not a completed comparison.
Original proof; no reference implementation copied. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison.FrobeniusStages

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeInterface : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def stage00_base :=
  LocalizationFrobeniusNaturality.commutes_equiv
    (Submonoid.powers (InitialThetaBoundedWittLocalization.denominator D w))
    (InitialThetaBoundedWittLocalization.inclusion D w)
    (PadicBoundedWittLocalization.inclusion (Arithmetic.residueChar w.1))
    (fun _ => rfl)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison.FrobeniusStages
