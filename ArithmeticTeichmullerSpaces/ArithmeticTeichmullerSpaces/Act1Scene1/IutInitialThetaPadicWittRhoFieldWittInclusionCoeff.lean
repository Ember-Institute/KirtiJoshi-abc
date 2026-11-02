import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittCoefficientSquare

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-INCLUSION-COEFFICIENT
source: the proved actual/standard tilt integer coefficient formula.
fidelity: exposes the coefficient equation in the original integerEquiv_apply
direction, with the exact functions
inferred by the generic Witt comparison. The two Witt carriers and their
coefficient maps are unchanged; no norm or compatibility law is input.
Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

set_option linter.defProp false

def fieldWittEquiv_wittInclusion_coeff :=
  InitialThetaPadicWittCoefficientSquare.mappedCoeff D w

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
