import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittActualBPlusCandidate

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ACTUAL-BPLUS-COORDINATE-SEMINORM
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, for the
rho-family on the period carrier.
fidelity: proves that the actual rho=1 unit-ball embedding into the common
all-radius completion preserves every coordinate seminorm exactly. The proof
uses the original embedding and the original completion inclusion norm law.
boundary: Scene1/Derived; this is an actual all-radius seminorm statement.
It does not identify the carrier with paper B or its rho norm, and does not
provide H1e/BK or holomorphoid laws. Original proof; no reference
implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittActualBPlusCandidate

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion
open InitialThetaWittAllRadiusCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := InitialThetaWittRhoCompletion.Radius

theorem unitBallToCommon_coordinateSeminorm (ρ : Radius)
    (x : unitBallSubring D w) :
    coordinateSeminorm D w ρ (unitBallToCommon D w x) =
      InitialThetaWittRhoNorm.realValue D w ρ.val x.1 := by
  rw [unitBallToCommon_apply]
  exact coordinateSeminorm_inclusion D w ρ x.1

end
end JoshiTeich.Act1Scene1.InitialThetaWittActualBPlusCandidate
