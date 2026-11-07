import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittActualBPlusCandidate

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ACTUAL-BPLUS-PADICINT-ALG-EQUIV
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, for the
integral scalar subring of the rho=1 unit ball.
fidelity: upgrades the actual rho=1 unit-ball Frobenius RingEquiv with the
existing PadicInt scalar law. The carrier, scalar map, and Frobenius map are
the original project constructions.
boundary: Scene1/Derived; this is a PadicInt-algebra equivalence for the
actual unit-ball candidate. It does not identify the carrier with paper B+
or B, and does not provide paper rho, Galois, H1e/BK, or holomorphoid laws.
Original proof; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittActualBPlusCandidate

open JoshiTeich.Prologue
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeAlgEquiv : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev UnitBall := unitBallSubring D w
def unitBallFrobeniusAlgEquiv :
    UnitBall D w ≃ₐ[PadicInt (Arithmetic.residueChar w.1)] UnitBall D w where
  __ := unitBallFrobeniusEquiv D w
  commutes' := by
    intro a
    exact unitBallFrobenius_padicInt D w a

theorem unitBallFrobeniusAlgEquiv_apply (x : UnitBall D w) :
    unitBallFrobeniusAlgEquiv D w x = unitBallFrobenius D w x :=
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittActualBPlusCandidate
