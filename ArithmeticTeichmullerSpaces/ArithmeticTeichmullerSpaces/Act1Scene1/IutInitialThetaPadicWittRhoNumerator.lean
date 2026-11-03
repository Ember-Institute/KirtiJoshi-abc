import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedCoefficientPower
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoCoefficientNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-NUMERATOR
source: Joshi II `se:ff-rings` and the proved local-degree norm law
and integer-ring comparison of the actual and independent standard tilt.
fidelity: compares weighted values of the original named integral Witt
numerators from their coefficient norms. The two coefficient norms and local-degree radius
change remain the original ones. No completed carrier is identified.
Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

open JoshiTeich.Prologue
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeNumerator : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance actualRawFieldNumerator : Field (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltField.carrierField D w
local instance standardRawFieldNumerator : Field (InitialThetaPadicTiltTopology.Standard D w) :=
  FractionRing.field (PadicTiltField.Source (Arithmetic.residueChar w.1))
local instance actualNormedFieldNumerator : NormedField (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltTopology.carrierNormedField D w
local instance standardNormedFieldNumerator : NormedField (InitialThetaPadicTiltTopology.Standard D w) :=
  PadicTiltField.carrierNormedField (Arithmetic.residueChar w.1)

set_option linter.defProp false in
def numerator_value_pow :=
  WittWeightedCoefficientPower.value_pow_of_coeff_norm_function
    (Arithmetic.residueChar w.1) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficient_inclusion_norm_pow D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
