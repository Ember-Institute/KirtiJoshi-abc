import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoFieldWittEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.FractionRingEquiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-AMBIENT-EQUIV
source: Joshi II se:ff-rings; the proved actual/standard tilt Witt equivalence.
fidelity: extends the coefficientwise Witt equivalence to the original
fraction-ring carriers. The full result type is inferred from the input
equivalence to preserve its ring instances. This does not identify the
bounded localizations, rho values, or completed paper B. Original proof;
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeAmbientEquiv : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def ambientEquiv :=
  JoshiTeich.Act1Scene1.fractionRingEquiv
    (fieldWittEquiv D w)

set_option linter.defProp false in
def ambientEquiv_algebraMap :=
  JoshiTeich.Act1Scene1.fractionRingEquiv_algebraMap (fieldWittEquiv D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
