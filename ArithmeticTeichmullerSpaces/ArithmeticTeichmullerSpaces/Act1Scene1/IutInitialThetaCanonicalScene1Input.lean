import ArithmeticTeichmullerSpaces.Act1Scene1.Boundary
import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u

noncomputable section

/-!
source-id: IUT-COR312-CANONICAL-SCENE1-INPUT
source: `InitialThetaData.prime.tate`, the canonical
`AdelicThetaLinkData.ofInitialThetaData`, and the public Scene1 input
contracts.
fidelity: fixes the Scene1 input carrier to the link constructed from the
same actual `InitialThetaData`.  The theta payload, packet/hull payload,
height, ramification, volume, and finite q-family accounting remain explicit
Scene1 data; this constructor does not prove those analytic obligations.
boundary: Scene1/Derived

The previous generic Scene1 boundary allowed an independently supplied link
and later required an equality certificate to the canonical IUT link.  This
payload makes the canonical link part of the construction, so its places,
Tate parameters, q-norm compatibility, and `j` source cannot be detached at
the call site.
-/

structure CanonicalInitialThetaScene1Input
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ) where
  placeData : PerfectoidPlaceData D.F O p
  bridge : PerfectoidBridgeData
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
    p placeData
  inputLaws :
    PrologueInputLaws p
      { link := AdelicThetaLinkData.ofInitialThetaData D theta thetaBase
          packetHull heightData ramification logVolume processionLength
        placeData := placeData
        bridge := bridge }
  adelicThetaLink : AdelicThetaLink
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
  thetaLiftLog : ThetaLiftLog
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
  packetCollationHull : PacketCollationHull
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
  volumeTransfer : VolumeTransfer
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength)

namespace CanonicalInitialThetaScene1Input

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (theta : ThetaPilotData D.F) (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (logVolume : ℝ) (processionLength : ℕ)

noncomputable def toScene1Input
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    Scene1Input D.F O p :=
  { data :=
      { link := AdelicThetaLinkData.ofInitialThetaData D theta thetaBase
          packetHull heightData ramification logVolume processionLength
        placeData := X.placeData
        bridge := X.bridge }
    input_laws := X.inputLaws
    adelic_theta_link := X.adelicThetaLink
    theta_lift_log := X.thetaLiftLog
    packet_collation_hull := X.packetCollationHull
    volume_transfer := X.volumeTransfer }

theorem toScene1Input_link_eq
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    (toScene1Input p D theta thetaBase packetHull heightData ramification
      logVolume processionLength X).data.link =
      AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength := by
  rfl

noncomputable def toData
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
    (ellStar : ℕ) (qIndex : Type u)
    (qIndexFintype : Fintype qIndex)
    (qLogTerm : qIndex → ℝ) (thetaVolume : ℝ) :
    Corollary312Data (K := D.F) (O := O) p :=
  { scene1 := toScene1Input p D theta thetaBase packetHull heightData
      ramification logVolume processionLength X
    ell := D.prime.ℓ
    ellStar := ellStar
    qIndex := qIndex
    qIndexFintype := qIndexFintype
    qLogTerm := qLogTerm
    thetaVolume := thetaVolume }

theorem toData_link_eq
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
    (ellStar : ℕ) (qIndex : Type u)
    (qIndexFintype : Fintype qIndex)
    (qLogTerm : qIndex → ℝ) (thetaVolume : ℝ) :
    (toData p D theta thetaBase packetHull heightData ramification logVolume
      processionLength X ellStar qIndex qIndexFintype qLogTerm thetaVolume).scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength := by
  rfl

end CanonicalInitialThetaScene1Input

end

end JoshiTeich.Act1Scene1
