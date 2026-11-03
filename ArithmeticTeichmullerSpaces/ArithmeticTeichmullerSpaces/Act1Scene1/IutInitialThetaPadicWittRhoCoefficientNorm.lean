import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-COEFFICIENT-NORM
source: Joshi II `se:ff-rings` and the original integer coefficient norm law.
fidelity: compares norms of original field-Witt coefficients through the
two existing integral inclusions. Original proof; Prologue R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeCoefficientNorm : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def coefficient_inclusion_norm_pow :=
  (InitialThetaPadicBoundedWittComparison.choicePresentationData D w).coeff_norm_pow

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
