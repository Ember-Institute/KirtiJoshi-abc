import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusNaturality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrobeniusSource

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-BOUNDED-WITT-FROBENIUS-ACTUAL-MAP-CACHED
source: Joshi II `se:ff-rings`, original actual bounded Frobenius map.
fidelity: names the original actual-then-standard ring hom separately from
the standard target wrapper. The original equivalence, Frobenius map, carrier
and operation dictionaries are retained. No comparison law is assumed.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: bounded map wrapper only; completion and paper B, period and BK
identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeCachedActualMap :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def actualThenStandardFrobeniusCached :
    InitialThetaBoundedWittLocalization.Ring D w →+*
      PadicBoundedWittLocalization.Ring (Arithmetic.residueChar w.1) :=
  (ringEquiv D w).toRingHom.comp
    (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).toRingHom

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
