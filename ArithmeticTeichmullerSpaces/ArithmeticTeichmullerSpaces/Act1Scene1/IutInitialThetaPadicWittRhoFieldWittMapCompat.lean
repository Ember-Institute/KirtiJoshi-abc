import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoFieldWittInclusionCoeff

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-MAP-COMPATIBILITY
source: the proved actual/standard coefficient square.
fidelity: consumes the generic Witt extensionality proof with its complete
inferred type. The equation retains the integerEquiv_apply direction.
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

def fieldWittEquiv_wittInclusion_mapCompat :=
  InitialThetaPadicWittCoefficientSquare.mappedSquare D w

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
