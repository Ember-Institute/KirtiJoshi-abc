import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSectionLink
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberAccounting

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
source-id: JT-SCENE1-INITIAL-THETA-SECTION-LINK-PRIME-FIBER-ACCOUNTING
source: the actual odd Tate section link carrier and the concrete
section/Voss prime fibers from `IutInitialThetaSectionLink.lean` and
`IutInitialThetaPaperVossPrimeFiberAccounting.lean`.
fidelity: identifies the finite place subtype of the link constructed from
the same InitialThetaData with the concrete section/Voss subtype, then
transfers its exact prime-fiber cardinality sum.
boundary: this is a same-source concrete carrier equivalence. It does not
identify the carrier with paper `L'` representatives, paper multiplicities,
omitted mass, or mixed-moduli descent.
-/

/-- The finite place type of the odd Tate section link. -/
abbrev iutInitialThetaOddTateSectionLinkPlaceType :=
  {w : NumberField.FinitePlace ↥D.prime.torsionField //
    w ∈ (AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
      packetHull heightData ramification logVolume processionLength).places}

noncomputable instance iutInitialThetaOddTateSectionLinkPlaceTypeFintype :
    Fintype (iutInitialThetaOddTateSectionLinkPlaceType D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :=
  Fintype.ofFinset
    (AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase packetHull
      heightData ramification logVolume processionLength).places
    (fun _ => Iff.rfl)

/-- The same-source link place subtype is equivalent to the concrete section/Voss subtype. -/
noncomputable def iutInitialThetaOddTateSectionLinkPlaceEquiv :
    iutInitialThetaOddTateSectionLinkPlaceType D theta thetaBase packetHull
      heightData ramification logVolume processionLength ≃
      {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaSectionVoss D} := by
  let hPlaces := iutInitialThetaOddTateSectionLink_places_eq_sectionVoss
    D theta thetaBase packetHull heightData ramification logVolume processionLength
  refine Equiv.ofBijective (fun w => ⟨w.1, ?_⟩) ?_
  · exact (Set.ext_iff.mp hPlaces w.1).mp (Finset.mem_coe.mpr w.2)
  constructor
  · intro w₁ w₂ h
    apply Subtype.ext
    exact congrArg (fun x => x.1) h
  · rintro ⟨w, hw⟩
    refine ⟨⟨w, ?_⟩, ?_⟩
    · exact (Set.ext_iff.mp hPlaces w).mpr hw
    · rfl

theorem iutInitialThetaOddTateSectionLinkPlace_card_eq_sectionVoss_card :
    Fintype.card
        (iutInitialThetaOddTateSectionLinkPlaceType D theta thetaBase packetHull
          heightData ramification logVolume processionLength) =
      Fintype.card {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaSectionVoss D} := by
  exact Fintype.card_congr
    (iutInitialThetaOddTateSectionLinkPlaceEquiv D theta thetaBase packetHull
      heightData ramification logVolume processionLength)

theorem iutInitialThetaOddTateSectionLinkPlace_card_eq_primeFiber_sum :
    Fintype.card
        (iutInitialThetaOddTateSectionLinkPlaceType D theta thetaBase packetHull
          heightData ramification logVolume processionLength) =
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D,
        iutInitialThetaSectionVossPrimeMultiplicity D p.1 := by
  rw [iutInitialThetaOddTateSectionLinkPlace_card_eq_sectionVoss_card
    D theta thetaBase packetHull heightData ramification logVolume processionLength,
    iutInitialThetaSectionVoss_card_eq_primeFiber_sum D]

theorem iutInitialThetaOddTateSectionLinkPlaceEquiv_residueChar (w :
    iutInitialThetaOddTateSectionLinkPlaceType D theta thetaBase packetHull
      heightData ramification logVolume processionLength) :
    Arithmetic.residueChar
        (iutInitialThetaOddTateSectionLinkPlaceEquiv D theta thetaBase packetHull
          heightData ramification logVolume processionLength w).1 =
      Arithmetic.residueChar w.1 := by
  rfl

end
end JoshiTeich.Act1Scene1
