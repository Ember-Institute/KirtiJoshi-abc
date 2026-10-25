import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootPaperQSum
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddTateSectionLinkPrimeFiberAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (theta : ThetaPilotData ↥D.prime.torsionField)
variable (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index)
variable (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
variable (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
variable (logVolume : ℝ) (processionLength : ℕ)

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-QROOT-LINK-PRIME-FIBER-ACCOUNTING
source: the selected q-root source/link equivalence from
`IutInitialThetaSelectedQRootPaperQSum.lean`, together with the concrete
section/Voss prime-fiber accounting.
fidelity: records the exact finite cardinality transfer from the section-
selected q-root source to the same-source odd Tate section link and then to
the Voss prime-fiber sum.
boundary: this is selected actual-carrier accounting. It does not construct
paper `L'` representatives, paper multiplicities, omitted mass, or mixed-
moduli descent.
-/

abbrev iutInitialThetaSelectedQRootLinkSourcePlaceType :=
  {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}

noncomputable instance iutInitialThetaSelectedQRootLinkSourcePlaceTypeFintype :
    Fintype (iutInitialThetaSelectedQRootLinkSourcePlaceType D) :=
  (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype

theorem iutInitialThetaSelectedQRootLinkSourcePlace_card_eq_link_card :
    Fintype.card (iutInitialThetaSelectedQRootLinkSourcePlaceType D) =
      Fintype.card
        (iutInitialThetaOddTateSectionLinkPlaceType D theta thetaBase packetHull
          heightData ramification logVolume processionLength) := by
  exact Fintype.card_congr
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_sectionLinkEquiv
      D theta thetaBase packetHull heightData ramification logVolume processionLength)

theorem iutInitialThetaSelectedQRootLinkSourcePlace_card_eq_primeFiber_sum
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    Fintype.card (iutInitialThetaSelectedQRootLinkSourcePlaceType D) =
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D,
        iutInitialThetaSectionVossPrimeMultiplicity D p.1 := by
  rw [iutInitialThetaSelectedQRootLinkSourcePlace_card_eq_link_card
    D theta thetaBase packetHull heightData ramification logVolume processionLength,
    iutInitialThetaOddTateSectionLinkPlace_card_eq_primeFiber_sum
      D theta thetaBase packetHull heightData ramification logVolume processionLength]

end
end JoshiTeich.Act1Scene1
