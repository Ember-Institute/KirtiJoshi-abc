import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootLinkAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSectionLink
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFieldOrientation

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open TateCurvesTheta

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-SELECTED-FIELD-ORIENTATION
source: the actual `InitialThetaData` section, the selected q-root source,
and `AdelicThetaLinkData.ofInitialThetaOddTateSection`.
fidelity: restricts the full torsion q-root source to the finite carrier
selected by the actual section and proves the field-orientation audit for the
canonical selected-section link. The local equality between the selected
q-root power and the section Tate parameter is an explicit source certificate;
the independent Scene1 link equality and prime-index alignment remain explicit.
boundary: Scene1/Derived
-/

def iutInitialThetaOddSupportSelectedQRootFinset
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Finset (NumberField.FinitePlace ↥D.prime.torsionField) :=
  (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).toFinset

private theorem iutInitialThetaOddSupportSelectedQRootFinset_coe_eq_source_image
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (↑(iutInitialThetaOddSupportSelectedQRootFinset D) :
        Set (NumberField.FinitePlace ↥D.prime.torsionField)) =
      (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset => s.1) ''
        iutInitialThetaOddSupportSelectedQRootSourcePlaces D := by
  ext w
  constructor
  · intro hw
    have hwSelected : w ∈ iutInitialThetaOddSupportSelectedQRootPlaces D :=
      (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).mem_toFinset.mp hw
    rcases hwSelected with ⟨v, hv, h⟩
    refine ⟨iutInitialThetaOddSupportSelectedQRootPlace D v hv, ?_, h⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).mem_toFinset.mpr hs

private noncomputable def iutInitialThetaOddSupportSelectedQRootWitness
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : (iutInitialThetaOddSupportSelectedQRootFinset D)) :
    {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D ∧ s.1 = v.1} := by
  classical
  have hv : v.1 ∈ iutInitialThetaOddSupportSelectedQRootPlaces D :=
    (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).mem_toFinset.mp v.2
  let w := Classical.choose hv
  have hw := Classical.choose_spec hv
  have hmem : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
    let q := iutInitialThetaOddSupportSelectedQRootPlace D w hw.1
    rw [← hw.2]
    exact q.2
  refine ⟨⟨v.1, hmem⟩, ?_, rfl⟩
  change ∃ (w : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
      (hw : w ∈ iutVBadOddModSupportPort D),
      (iutInitialThetaOddSupportSelectedQRootPlace D w hw).1 = v.1
  exact ⟨w, hw.1, hw.2⟩

noncomputable def iutInitialThetaOddSupportSelectedQRootAt
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddSupportSelectedQRootFinset D) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
  let s := iutInitialThetaOddSupportSelectedQRootWitness D v
  exact ⟨v.1, by rw [← s.2.2]; exact s.1.2⟩

private theorem iutInitialThetaOddSupportSelectedQRootAt_eq_witness
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddSupportSelectedQRootFinset D) :
    iutInitialThetaOddSupportSelectedQRootAt D v =
      (iutInitialThetaOddSupportSelectedQRootWitness D v).1 := by
  apply Subtype.ext
  simpa [iutInitialThetaOddSupportSelectedQRootAt] using
    (iutInitialThetaOddSupportSelectedQRootWitness D v).2.2.symm

noncomputable def iutInitialThetaOddSupportSelectedQRootQRoot
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddSupportSelectedQRootFinset D) :
    v.1.maximalIdeal.adicCompletion (↥D.prime.torsionField) := by
  simpa [iutInitialThetaOddSupportSelectedQRootAt] using
    (iutInitialThetaOddSupportTorsionQRootSource D).qroot
      (iutInitialThetaOddSupportSelectedQRootAt D v)

theorem IutFieldOrientationAudit.ofInitialThetaSelectedTateSection
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data (↥D.prime.torsionField) O p}
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (hSelectedParameter :
      ∀ v : iutInitialThetaOddSupportSelectedQRootFinset D,
        iutInitialThetaOddSupportSelectedQRootQRoot D v ^
            (2 * D.prime.ℓ) =
          (iutInitialThetaOddTateSectionTateParameterData D).parameter v.1)
    (hEll : T.ell = D.prime.ℓ)
    (hLink : T.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
        packetHull heightData ramification logVolume processionLength) :
    ∃ (B : IutBaseQPilotSource D.F T.ell)
      (R : IutTorsionQRootSource D.F (↥D.prime.torsionField) T.ell B),
      IutFieldOrientationAudit p T B R := by
  let B0 := iutInitialThetaOddSupportBaseQPilotSource D
  let R0 := iutInitialThetaOddSupportTorsionQRootSource D
  let B : IutBaseQPilotSource D.F T.ell :=
    { badPlaces := B0.badPlaces
      badFinset := B0.badFinset
      badFinset_spec := B0.badFinset_spec
      weight := B0.weight
      weight_eq_qPilotWeight := B0.weight_eq_qPilotWeight
      tateParameter := B0.tateParameter
      tateParameter_ne_zero := B0.tateParameter_ne_zero
      tateParameter_norm_lt_one := B0.tateParameter_norm_lt_one }
  let R : IutTorsionQRootSource D.F (↥D.prime.torsionField) T.ell B :=
    { badFinset := iutInitialThetaOddSupportSelectedQRootFinset D
      basePlace := fun v =>
        R0.basePlace (iutInitialThetaOddSupportSelectedQRootAt D v)
      liesOver := fun v =>
        by simpa [iutInitialThetaOddSupportSelectedQRootAt] using
          R0.liesOver (iutInitialThetaOddSupportSelectedQRootAt D v)
      qroot := fun v =>
        iutInitialThetaOddSupportSelectedQRootQRoot D v
      qroot_ne_zero := fun v => by
        change R0.qroot (iutInitialThetaOddSupportSelectedQRootAt D v) ≠ 0
        exact R0.qroot_ne_zero (iutInitialThetaOddSupportSelectedQRootAt D v)
      completionMap := fun v => by
        exact iutEmbedCompletion (by
          simpa [iutInitialThetaOddSupportSelectedQRootAt] using
            R0.liesOver (iutInitialThetaOddSupportSelectedQRootAt D v))
      qroot_pow_eq := fun v => by
        change R0.qroot (iutInitialThetaOddSupportSelectedQRootAt D v) ^ (2 * T.ell) =
          R0.completionMap (iutInitialThetaOddSupportSelectedQRootAt D v)
            (B0.tateParameter (R0.basePlace
              (iutInitialThetaOddSupportSelectedQRootAt D v)))
        simpa [R0, B0, iutInitialThetaOddSupportSelectedQRootAt, hEll] using
          R0.qroot_pow_eq (iutInitialThetaOddSupportSelectedQRootAt D v) }
  refine ⟨B, R, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hLink]
    apply Finset.ext
    intro w
    have hSource := Set.ext_iff.mp
      (iutInitialThetaOddSupportSelectedQRootFinset_coe_eq_source_image D) w
    have hLinkPlaces := Set.ext_iff.mp
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionLinkPlaces
        D theta thetaBase packetHull heightData ramification logVolume processionLength) w
    exact hSource.trans hLinkPlaces
  · intro v
    rw [hLink]
    calc
      R.completionMap v (B.tateParameter (R.basePlace v)) =
          R.qroot v ^ (2 * T.ell) := (R.qroot_pow_eq v).symm
      _ = (iutInitialThetaOddTateSectionTateParameterData D).parameter v.1 := by
        change iutInitialThetaOddSupportSelectedQRootQRoot D v ^ (2 * T.ell) =
          (iutInitialThetaOddTateSectionTateParameterData D).parameter v.1
        simpa [hEll] using hSelectedParameter v

end

end JoshiTeich.Act1Scene1
