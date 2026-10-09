import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSectionLink

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-SELECTED-QROOT-LINK-CARRIER
source: the actual `InitialThetaData` section and the constructed
`AdelicThetaLinkData.ofInitialThetaOddTateSection` carrier.
fidelity: the selected q-root source's underlying finite-place image is
identified with the finite-place carrier of the canonical Scene1 link built
from the same section. This consumes the concrete section `underline V^oss`
identity and does not identify an independently supplied link.
boundary: Scene1/Derived
-/

/-! The source carrier and the canonical section link have the same finite
place carrier, with all analytic link data kept explicit. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionLinkPlaces
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset => s.1) ''
        iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
      (↑(AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
        packetHull heightData ramification logVolume processionLength).places :
        Set (NumberField.FinitePlace ↥D.prime.torsionField)) := by
  calc
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset => s.1) ''
          iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
        iutInitialThetaSectionVoss D :=
      iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionVoss D
    _ = (↑(AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
        packetHull heightData ramification logVolume processionLength).places :
        Set (NumberField.FinitePlace ↥D.prime.torsionField)) :=
      (iutInitialThetaOddTateSectionLink_places_eq_sectionVoss D theta thetaBase
        packetHull heightData ramification logVolume processionLength).symm

end

end JoshiTeich.Act1Scene1
