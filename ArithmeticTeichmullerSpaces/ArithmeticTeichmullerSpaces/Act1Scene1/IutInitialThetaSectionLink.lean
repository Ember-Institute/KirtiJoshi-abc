import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.QNormTateBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-SECTION-LINK
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean`,
`ValuationSection.sectFin`; `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`tateFamilyOfTorsion`; Joshi–Teich, *Arithmetic Teichmuller Spaces III*,
`ss:theta-data-fixing2`, `ss:val-sets-defn`, and `cor:cor312`.
fidelity: constructs a finite Tate-parameter carrier from the local Tate
structures at the actual section representatives of the complete odd
multiplicative support. The resulting link's places are exactly the odd Tate
section locus characterized in `IutInitialThetaVoss`. The theta, packet/hull,
height, ramification, and volume data remain explicit. This does not identify
an independently supplied Scene1 link with this constructed link.
boundary: Scene1/Derived
-/

private theorem iutInitialThetaOddSupportSelectedQRootPlaces_nonempty
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddSupportSelectedQRootPlaces D).Nonempty := by
  rcases D.global.bad_nonempty with ⟨v, hv⟩
  have hvSupport := iutInitialThetaVBad_subset_VBadOdd D hv
  refine ⟨iutInitialThetaFinitePlaceSection D v, ?_⟩
  rw [iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces,
    iutInitialThetaOddTateSectionPlaces_eq_selectedSupport,
    iutInitialThetaOddMultiplicativeSelectedPlaces]
  exact ⟨v, hvSupport, rfl⟩

/-- A Tate structure selected by the actual section at an odd support place. -/
noncomputable def iutInitialThetaOddTateSectionTateStructure
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace ↥D.prime.torsionField)
    (hw : w ∈ iutInitialThetaOddSupportSelectedQRootPlaces D) :
    JoshiTeich.ReferenceIut.TateStructure
      (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w) := by
  classical
  have hwSelected : w ∈ iutInitialThetaOddMultiplicativeSelectedPlaces D := by
    rw [iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces,
      iutInitialThetaOddTateSectionPlaces_eq_selectedSupport] at hw
    exact hw
  have hwImage : ∃ v, v ∈ iutVBadOddModSupportPort D ∧
      iutInitialThetaFinitePlaceSection D v = w := by
    simpa [iutInitialThetaOddMultiplicativeSelectedPlaces] using hwSelected
  let v := Classical.choose hwImage
  have hvImage := Classical.choose_spec hwImage
  rw [← hvImage.2]
  exact iutInitialThetaFinitePlaceSection_tateStructure D v hvImage.1

/-- Tate parameters on precisely the finite places selected by the actual
section over the complete odd multiplicative support. -/
noncomputable def iutInitialThetaOddTateSectionTateParameterData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Theta.TateParameterData ↥D.prime.torsionField := by
  classical
  let hfinite := iutInitialThetaOddSupportSelectedQRootPlaces_finite D
  let q : ∀ w : NumberField.FinitePlace ↥D.prime.torsionField,
      w.maximalIdeal.adicCompletion ↥D.prime.torsionField := fun w =>
    if hw : w ∈ iutInitialThetaOddSupportSelectedQRootPlaces D then
      ((iutInitialThetaOddTateSectionTateStructure D w hw).t.q :
        w.maximalIdeal.adicCompletion ↥D.prime.torsionField)
    else 0
  exact
    { places := hfinite.toFinset
      parameter := q
      norm := fun w => ‖q w‖ }

theorem iutInitialThetaOddTateSectionTateParameterData_parameter_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace ↥D.prime.torsionField)
    (hw : w ∈ iutInitialThetaOddSupportSelectedQRootPlaces D) :
    (iutInitialThetaOddTateSectionTateParameterData D).parameter w =
      (iutInitialThetaOddTateSectionTateStructure D w hw).t.q := by
  simp [iutInitialThetaOddTateSectionTateParameterData, hw]

theorem iutInitialThetaOddTateSectionTateParameterData_laws
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Theta.TateParameterLaws (iutInitialThetaOddTateSectionTateParameterData D) := by
  classical
  let hfinite := iutInitialThetaOddSupportSelectedQRootPlaces_finite D
  let T := iutInitialThetaOddTateSectionTateParameterData D
  constructor
  · rcases iutInitialThetaOddSupportSelectedQRootPlaces_nonempty D with ⟨w, hw⟩
    exact ⟨w, hfinite.mem_toFinset.mpr hw⟩
  · intro w hwFin
    have hw := hfinite.mem_toFinset.mp hwFin
    rw [iutInitialThetaOddTateSectionTateParameterData_parameter_eq D w hw]
    exact (iutInitialThetaOddTateSectionTateStructure D w hw).t.q.ne_zero
  · intro w hwFin
    rfl
  · intro w hwFin
    have hw := hfinite.mem_toFinset.mp hwFin
    change 0 < T.norm w
    rw [show T.norm w = ‖T.parameter w‖ by rfl,
      iutInitialThetaOddTateSectionTateParameterData_parameter_eq D w hw]
    exact (iutInitialThetaOddTateSectionTateStructure D w hw).t.norm_q_pos
  · intro w hwFin
    have hw := hfinite.mem_toFinset.mp hwFin
    change T.norm w < 1
    rw [show T.norm w = ‖T.parameter w‖ by rfl,
      iutInitialThetaOddTateSectionTateParameterData_parameter_eq D w hw]
    exact (iutInitialThetaOddTateSectionTateStructure D w hw).t.norm_lt_one

/-- Build an adelic link over the torsion field whose finite-place carrier is
the actual section's odd Tate locus. -/
noncomputable def AdelicThetaLinkData.ofInitialThetaOddTateSection
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    AdelicThetaLinkData ↥D.prime.torsionField :=
  AdelicThetaLinkData.ofTateParameters
    (iutInitialThetaOddTateSectionTateParameterData D) theta thetaBase packetHull
    heightData ramification logVolume processionLength

theorem iutInitialThetaOddTateSectionLink_places_eq_oddTateSectionPlaces
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    (↑(AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
      packetHull heightData ramification logVolume processionLength).places :
        Set (NumberField.FinitePlace ↥D.prime.torsionField)) =
      iutInitialThetaOddTateSectionPlaces D := by
  change (↑(iutInitialThetaOddTateSectionTateParameterData D).places :
    Set (NumberField.FinitePlace ↥D.prime.torsionField)) = _
  calc
    _ = iutInitialThetaOddSupportSelectedQRootPlaces D :=
      (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).coe_toFinset
    _ = iutInitialThetaOddTateSectionPlaces D :=
      iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces D

theorem iutInitialThetaOddTateSectionLink_qNormTateCompatibility
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    QNormTateCompatibility
      (AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
        packetHull heightData ramification logVolume processionLength) :=
  qNormTateCompatibility_of_tateParameters
    (iutInitialThetaOddTateSectionTateParameterData D) theta thetaBase packetHull
    heightData ramification logVolume processionLength

end

end JoshiTeich.Act1Scene1
