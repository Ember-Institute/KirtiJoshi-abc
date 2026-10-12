import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQPilot

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-CANONICAL-SOURCE-FIELD-AUDIT
source: `InitialThetaData.prime.tate`, the canonical link
`AdelicThetaLinkData.ofInitialThetaData`, and the proved finite carrier
identity `iutInitialThetaLink_places_eq_badPlacesOver`.
fidelity: derives the carrier and local parameter inputs of the q-pilot
constructor from equality of the target Tate data with the actual canonical
Tate data. Q-norm compatibility remains explicit. This does not construct
packet, hull, or volume accounting.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-- Both parameter families use the same actual admissible-prime parameter. -/
theorem iutCanonicalBaseSource_tateParameter_eq_link
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (w : (IutBaseQPilotSource.ofInitialThetaData D).badFinset) :
    (IutBaseQPilotSource.ofInitialThetaData D).tateParameter w =
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength).tate.parameter w.1 := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  have hwBad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    B.mem_badPlaces w
  have hwLink : w.1 ∈
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength).places := by
    have h := iutInitialThetaLink_places_eq_badPlacesOver D theta thetaBase
      packetHull heightData ramification logVolume processionLength
    exact (Set.ext_iff.mp h w.1).mp hwBad
  have hB : B.tateParameter w = (D.prime.tate w.1 hwBad).q := rfl
  exact hB.trans (iutInitialThetaLink_parameter_eq_prime_tate D theta thetaBase
    packetHull heightData ramification logVolume processionLength hwLink hwBad).symm

/-- The derived integer orders agree because their completion elements agree. -/
theorem iutCanonicalBaseSource_qOrder_eq_link
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (w : (IutBaseQPilotSource.ofInitialThetaData D).badFinset) :
    (IutBaseQPilotSource.ofInitialThetaData D).qOrder w =
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength).tate.qOrder w.1 := by
  exact congrArg (Arithmetic.completionQOrder w.1)
    (iutCanonicalBaseSource_tateParameter_eq_link D theta thetaBase
      packetHull heightData ramification logVolume processionLength w)

/-- Construct the actual q-pilot source from its Tate fields. Carrier equality,
parameter equality, and the Tate j-identity are derived by the constructor. -/
noncomputable def IutQPilotSource.ofInitialThetaCanonicalTateData
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (hEll : T.ell = D.prime.ℓ)
    (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutQPilotSource p T := by
  let L := T.scene1.data.link
  have hPlaces : JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      (↑L.places : Set (FinitePlace D.F)) := by
    rw [hCompat.places_eq, hTate]
    exact iutInitialThetaTateParameterData_places_eq D
  have hParameter : ∀ w : (IutBaseQPilotSource.ofInitialThetaData D).badFinset,
      (IutBaseQPilotSource.ofInitialThetaData D).tateParameter w =
        L.tate.parameter w.1 := by
    intro w
    rw [hTate]
    exact iutCanonicalBaseSource_tateParameter_eq_link D L.theta L.thetaBase
      L.packetHull L.heightData L.ramification L.logVolume L.processionLength w
  exact IutQPilotSource.ofInitialThetaData_of_parameter_eq D p
    hEll hPlaces hParameter hCompat

end
end JoshiTeich.Act1Scene1
