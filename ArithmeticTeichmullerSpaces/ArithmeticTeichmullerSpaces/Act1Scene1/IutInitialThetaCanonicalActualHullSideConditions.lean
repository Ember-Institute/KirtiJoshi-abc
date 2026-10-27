import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullQProductBounds

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-SIDE-CONDITIONS
source: the admissible-prime laws, actual-hull q-product positivity, and
actual-hull volume lower bound already proved in Scene1.
fidelity: constructs the explicit Corollary 3.12 side-condition bundle for
the canonical actual-hull target. It does not prove the target inequality's
paper interpretation or the missing producer identities.
boundary: Scene1/Derived; analytic input and paper normalization remain
explicit.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.SideConditions

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O]
variable (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (theta : ThetaPilotData D.F)
variable (route : CanonicalActualHull.PositivePacket D → theta.index)
variable (thetaBase : theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (X : CanonicalActualHull.AnalyticInput (O := O) p D theta route thetaBase
  heightData ramification)

local instance selectedPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

abbrev Target := CanonicalActualHull.data p D theta route thetaBase heightData ramification X

theorem sideConditions :
    Corollary312SideConditions p (Target p D theta route thetaBase heightData ramification X) := by
  refine
    { ell_prime := D.prime.ℓ_prime
      ell_ge_five := D.prime.five_le
      ellStar_eq_half_sub_one := by rfl
      ellStar_pos := CanonicalActualHull.length_pos D
      thetaVolume_pos := ?_ }
  exact lt_of_lt_of_le
    (CanonicalActualHull.QProductBounds.qProduct_pos p D theta route thetaBase heightData ramification X)
    (CanonicalActualHull.thetaVolume_ge_qProduct p D theta route thetaBase heightData ramification X)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.SideConditions
