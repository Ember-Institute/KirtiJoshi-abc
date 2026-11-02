import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicTiltTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.WittCoefficientSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.WittFractionCoefficientSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.WittComparisonData

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-COEFFICIENT-SQUARE
source: the proved integerEquiv_apply formula for the actual/standard tilt.
fidelity: preserves the exact inferred functions of the coefficient
comparison, and constructs compatible Witt and fraction-ring comparison
data using the proved abstract constructors.
Original proofs; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittCoefficientSquare

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeSquare : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false

def coeff := WittCoefficientSquare.coeff (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.integerEquiv_apply D w)

def square := WittCoefficientSquare.square (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.integerEquiv_apply D w)

def mappedCoeff := WittFractionCoefficientSquare.coeff (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.ringEquiv D w)
  (InitialThetaPadicTiltTopology.integerEquiv_apply D w)

def mappedSquare := WittFractionCoefficientSquare.square (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.ringEquiv D w)
  (InitialThetaPadicTiltTopology.integerEquiv_apply D w)

def comparisonData := WittComparisonData.ofSquare (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.ringEquiv D w)
  (InitialThetaPadicTiltTopology.integerEquiv_apply D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittCoefficientSquare
