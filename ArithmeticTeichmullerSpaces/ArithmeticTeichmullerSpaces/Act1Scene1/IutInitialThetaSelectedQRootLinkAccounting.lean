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

theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_card_eq_sectionLinkPlaces_card
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
      packetHull heightData ramification logVolume processionLength
    let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
    letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    letI : Fintype W := Fintype.ofFinset L.places (fun _ => Iff.rfl)
    Fintype.card S = Fintype.card W := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
    packetHull heightData ramification logVolume processionLength
  let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  letI : Fintype W := Fintype.ofFinset L.places (fun _ => Iff.rfl)
  let e : S → W := fun s =>
    ⟨s.1.1, by
      have hImage := iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionLinkPlaces
        D theta thetaBase packetHull heightData ramification logVolume processionLength
      have hs : s.1.1 ∈ iutInitialThetaSectionVoss D := by
        rw [← iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionVoss D]
        exact ⟨s.1, s.2, rfl⟩
      have hsL : s.1.1 ∈ (↑L.places : Set _) := by
        rw [← hImage]
        exact ⟨s.1, s.2, rfl⟩
      exact hsL⟩
  have he : Function.Bijective e := by
    constructor
    · intro s t h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : W => x.1) h
    · intro w
      have hImage := iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionLinkPlaces
        D theta thetaBase packetHull heightData ramification logVolume processionLength
      have hw : w.1 ∈ (↑L.places : Set _) := w.2
      have hwImage : w.1 ∈
          (fun s : R.badFinset => s.1) ''
            iutInitialThetaOddSupportSelectedQRootSourcePlaces D := by
        rw [hImage]
        exact hw
      rcases hwImage with ⟨s, hs, hsw⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      exact hsw
  exact Fintype.card_congr (Equiv.ofBijective e he)

end

end JoshiTeich.Act1Scene1
