import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullData

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-SCENE1-COHERENCE
source: the actual arithmetic/Haar hull carrier and the canonical Scene1
input constructor built from one `InitialThetaData`.
fidelity: records the definitional coherence of the canonical link, place,
Fontaine bridge, perfectoid bridge law, and volume-transfer field as they pass
into `Scene1Input`.
boundary: Scene1/Derived; analytic fields remain explicit and this theorem
does not construct the missing global producer or paper identities.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.Scene1Coherence

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

abbrev S := CanonicalActualHull.scene1Input p D theta route thetaBase heightData ramification X
abbrev L := CanonicalActualHull.link D theta route thetaBase heightData ramification

theorem toCanonicalInput_placeData :
    (CanonicalActualHull.toCanonicalInput p D theta route thetaBase heightData ramification X).placeData =
      X.placeData := rfl

theorem toCanonicalInput_bridge :
    (CanonicalActualHull.toCanonicalInput p D theta route thetaBase heightData ramification X).bridge =
      X.bridge := rfl

theorem scene1Input_link_eq : (S p D theta route thetaBase heightData ramification X).data.link =
    AdelicThetaLinkData.ofInitialThetaData D theta thetaBase
      (CanonicalActualHull.packetHull D theta route) heightData ramification
      (cost D) (length D) := rfl

theorem scene1Input_bridge_eq :
    (S p D theta route thetaBase heightData ramification X).data.bridge = X.bridge := rfl

theorem scene1Input_perfectoidBridge_eq :
    (S p D theta route thetaBase heightData ramification X).input_laws.perfectoid_bridge =
      X.perfectoidBridge := rfl

theorem scene1Input_volumeTransfer_eq :
    (S p D theta route thetaBase heightData ramification X).producer_laws.volume_transfer =
      ActualHullCostTransfer.volumeTransfer D (length D) (tuple D) (tuple_liesOver D)
        (collation D) theta route
        (VBadThetaLogCollation.generator_coverage D (length D) (tuple D) (tuple_liesOver D))
        (VBadThetaLogCollation.collation_subset_normalization D (length D) (tuple D) (tuple_liesOver D))
        thetaBase heightData ramification := rfl

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.Scene1Coherence
