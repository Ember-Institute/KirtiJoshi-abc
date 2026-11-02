import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittCoefficientSquare

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-FIELD-WITT-EQUIV
source: the proved actual-to-standard initial theta padic tilt Witt
comparison.
fidelity: exposes the induced equivalence between the two Witt fraction
fields. Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

open JoshiTeich.Prologue
noncomputable section

universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def fieldWittEquiv :=
  (InitialThetaPadicWittCoefficientSquare.comparisonData D w).fieldEquiv

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
