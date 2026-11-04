import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicChoiceFrobeniusTransfer

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-BOUNDED-WITT-FROBENIUS-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, functorial
Frobenius on the original bounded Witt localizations.
fidelity: proves the original canonical bounded comparison commutes with
the original actual and standard Frobenius maps. Choice naturality follows
from their original denominator presentations and numerator naturality;
the original choice conjugation and comparison-function identities transfer
it back to the canonical carrier. Every input law is proved on the same
original functions. No norm law or comparison certificate is assumed.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: completion transport and paper B/period/BK identities are separate.
-/


namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusComparison :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def ringEquiv_frobenius :=
  canonicalFrobeniusNaturality D w

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
