import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittCoefficientSquare

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-FIELD-WITT-EQUIV
source: Joshi II `se:ff-rings` and the proved actual-to-standard tilt
ring equivalence.
fidelity: applies the original coefficient ring equivalence to the two
Witt rings over the coefficient fields, with the original field instances
fixed explicitly. Original proof; Scene1/Derived; Prologue R5 unchanged.
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

local instance actualCoefficientField : Field (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltField.carrierField D w

local instance standardCoefficientField : Field (PadicTiltField.Carrier (Arithmetic.residueChar w.1)) :=
  FractionRing.field (PadicTiltField.Source (Arithmetic.residueChar w.1))

def fieldWittEquiv :=
  WittRingEquiv.mapEquiv (Arithmetic.residueChar w.1)
    (InitialThetaPadicTiltTopology.ringEquiv D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
