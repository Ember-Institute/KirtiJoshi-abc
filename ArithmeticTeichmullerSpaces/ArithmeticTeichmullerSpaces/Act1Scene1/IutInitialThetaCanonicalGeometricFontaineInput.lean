import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalGeometricFontaine
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalScene1Input

/-!
source-id: JT-SCENE1-CANONICAL-GEOMETRIC-FONTAINE-INPUT
source: the actual supported `InitialThetaData` Tate place, the canonical
geometric Fontaine completion, and the `CanonicalInitialThetaScene1Input`
contract.
fidelity: supplies the actual local `PerfectoidPlaceData`, coefficient map,
and `PerfectoidBridgeLaws` to a canonical Scene1 input. Theta scaling, period,
normalization, packet/hull, and volume laws remain explicit analytic inputs.
boundary: Scene1/Derived. This is a local bridge adapter; it does not produce
the global holomorphoid, H¹ₑ/BK comparison, or paper theta-volume identity.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

namespace CanonicalInitialThetaScene1Input

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (theta : ThetaPilotData D.F) (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (logVolume : ℝ) (processionLength : ℕ)

local instance selectedPrime :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance selectedPrimeNorm :
    Fact (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w
local instance selectedPrimeNonunit :
    Fact (¬ IsUnit (Arithmetic.residueChar w.1 :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))) :=
  LocalGeometricFontaine.primeNonunitFact
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
    (Arithmetic.residueChar w.1)

noncomputable def ofCanonicalGeometricFontaine
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      logVolume = ∑ i, theta.period i)
    (packet_weight_positive : ∀ q, 0 < packetHull.packetWeight q)
    (hull_weight_positive : ∀ h, 0 < packetHull.hullWeight h)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i))
    (packetCollationHull : PacketCollationHull
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength))
    (volumeTransfer : VolumeTransfer
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength)) :
    CanonicalInitialThetaScene1Input
      (O := LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
      (Arithmetic.residueChar w.1) D theta thetaBase packetHull heightData
      ramification logVolume processionLength := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  refine
    { placeData := InitialThetaCanonicalGeometricFontaine.placeData D w
      bridge := InitialThetaCanonicalGeometricFontaine.bridgeData D w theta thetaBase
        packetHull heightData ramification logVolume processionLength
      thetaScaling := thetaScaling
      periodMap := periodMap
      normalization := normalization
      packet_weight_positive := packet_weight_positive
      hull_weight_positive := hull_weight_positive
      perfectoidBridge := InitialThetaCanonicalGeometricFontaine.bridgeData_laws D w theta thetaBase
        packetHull heightData ramification logVolume processionLength
      theta_log_shell := theta_log_shell
      packetCollationHull := packetCollationHull
      volumeTransfer := volumeTransfer }

theorem ofCanonicalGeometricFontaine_place_eq
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      logVolume = ∑ i, theta.period i)
    (packet_weight_positive : ∀ q, 0 < packetHull.packetWeight q)
    (hull_weight_positive : ∀ h, 0 < packetHull.hullWeight h)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i))
    (packetCollationHull : PacketCollationHull
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength))
    (volumeTransfer : VolumeTransfer
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength)) :
    let X := ofCanonicalGeometricFontaine (D := D) (w := w) theta thetaBase packetHull
      heightData ramification logVolume processionLength thetaScaling periodMap normalization
      packet_weight_positive hull_weight_positive theta_log_shell packetCollationHull
      volumeTransfer
    (X.placeData).place = w.1 := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rfl

end CanonicalInitialThetaScene1Input

end
end JoshiTeich.Act1Scene1
