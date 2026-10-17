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
  /-- The non-arithmetic theta scaling law is the remaining part of the
      adelic link contract after its valuation scaling is derived from the
      canonical Tate parameter. -/
  thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase
  periodMap : ∀ i, theta.period i = theta.liftedLog i
  normalization :
    letI := theta.indexFintype
    logVolume = ∑ i, theta.period i
  packet_weight_positive : ∀ q, 0 < packetHull.packetWeight q
  hull_weight_positive : ∀ h, 0 < packetHull.hullWeight h
  perfectoidBridge : PerfectoidBridgeLaws
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength)
    p
    placeData bridge
  theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)
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

private noncomputable def canonicalLink
    (_X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    AdelicThetaLinkData D.F :=
  AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
    heightData ramification logVolume processionLength

private theorem canonicalLink_valuation_scaling
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    ∀ w ∈ (canonicalLink p D theta thetaBase packetHull heightData ramification
      logVolume processionLength X).places, ∀ j : ℕ,
      (canonicalLink p D theta thetaBase packetHull heightData ramification
        logVolume processionLength X).qNorm w ^ (j * j) =
        ‖((canonicalLink p D theta thetaBase packetHull heightData ramification
          logVolume processionLength X).qParameter w) ^ (j * j)‖ := by
  intro w hw j
  simp only [canonicalLink, AdelicThetaLinkData.ofInitialThetaData,
    AdelicThetaLinkData.ofTateParameters, AdelicThetaLinkData.qNorm]
  rw [norm_pow]

private noncomputable def canonicalAdelicThetaLink
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    AdelicThetaLink (canonicalLink p D theta thetaBase packetHull heightData
      ramification logVolume processionLength X) :=
  { valuation_scaling := canonicalLink_valuation_scaling p D theta thetaBase
      packetHull heightData ramification logVolume processionLength X
    theta_scaling := X.thetaScaling
    period_map := X.periodMap
    normalization := X.normalization }

private noncomputable def canonicalInputLaws
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    PrologueInputLaws p
      { link := canonicalLink p D theta thetaBase packetHull heightData ramification
          logVolume processionLength X
        placeData := X.placeData
        bridge := X.bridge } := by
  let L := canonicalLink p D theta thetaBase packetHull heightData ramification
    logVolume processionLength X
  let T := iutInitialThetaTateParameterData_laws D
  let A := canonicalAdelicThetaLink p D theta thetaBase packetHull heightData
    ramification logVolume processionLength X
  refine
    { first_axiom := ?_
      tate_parameter := ?_
      adelic_theta_link := A
      perfectoid_bridge := X.perfectoidBridge }
  · refine
      { places_nonempty := T.places_nonempty
        q_parameter_nonzero := ?_
        q_norm_positive := ?_
        height_nonnegative := fun x => heightData.value_nonneg x
        theta_norm_positive := X.thetaScaling.norm_positive
        packet_weight_positive := ?_
        hull_weight_positive := ?_ }
    · intro w hw
      exact T.parameter_nonzero w hw
    · intro w hw
      exact T.norm_pos w hw
    · exact X.packet_weight_positive
    · exact X.hull_weight_positive
  · simpa [L, canonicalLink, AdelicThetaLinkData.ofInitialThetaData,
      AdelicThetaLinkData.ofTateParameters] using T

noncomputable def toScene1Input
    (X : CanonicalInitialThetaScene1Input (O := O) p D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    Scene1Input D.F O p :=
  { data :=
      { link := AdelicThetaLinkData.ofInitialThetaData D theta thetaBase
          packetHull heightData ramification logVolume processionLength
        placeData := X.placeData
        bridge := X.bridge }
    input_laws := canonicalInputLaws p D theta thetaBase packetHull heightData
      ramification logVolume processionLength X
    adelic_theta_link := canonicalAdelicThetaLink p D theta thetaBase packetHull
      heightData ramification logVolume processionLength X
    theta_lift_log :=
      { log_shell := X.theta_log_shell
        value_nonzero := X.thetaScaling.value_nonzero }
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
