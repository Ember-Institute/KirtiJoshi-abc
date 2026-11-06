import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusInterface
import ArithmeticTeichmullerSpaces.Act1Scene1.RingEquivDictionaryTransport

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-SOURCE-ADD
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the original bounded Witt localization.
fidelity: identifies only the source addition dictionary of the original
ring equivalence with the corresponding dictionary in the existing
Frobenius interface binder. The original carriers and functions are retained.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: Scene1/Derived; this atomic dictionary identity does not establish
Frobenius comparison or the paper B, period or BK identities.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison.FrobeniusDictionaries

open JoshiTeich.Prologue
noncomputable section
set_option warn.classDefReducibility false

universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeSourceAdd : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def originalSourceAdd := RingEquivDictionaryTransport.sourceAdd (ringEquiv D w)

def expectedSourceAdd := RingEquivDictionaryTransport.expectedSourceAdd
  (FrobeniusStages.stage00_base D w)

theorem sourceAdd_eq : originalSourceAdd D w = expectedSourceAdd D w := by
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison.FrobeniusDictionaries
