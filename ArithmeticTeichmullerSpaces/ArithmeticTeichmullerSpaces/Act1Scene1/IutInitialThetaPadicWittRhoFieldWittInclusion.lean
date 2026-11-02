import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoFieldWittMapCompat
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoFieldWittEquiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-FIELD-WITT-INCLUSION
source: the coefficient formula for the actual-to-standard tilt Witt
comparison and the existing integer-ring equivalence.
fidelity: proves compatibility of the field-Witt equivalence with the
integral Witt inclusion functions by checking each Witt coefficient. The
complete inferred function interface avoids repeating concrete ring-instance
conversion; adaptation to the named bounded-localization toAmbient maps
remains a separate downstream obligation. Original proof;
Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

noncomputable section

universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

set_option linter.defProp false

def fieldWittEquiv_wittInclusion := fieldWittEquiv_wittInclusion_mapCompat D w

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
