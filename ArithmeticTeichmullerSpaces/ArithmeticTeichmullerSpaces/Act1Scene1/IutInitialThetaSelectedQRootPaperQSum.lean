import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootLinkAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedFieldOrientation

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open TateCurvesTheta
open scoped BigOperators

universe u

noncomputable section

/-!
source-id: IUT-COR312-SELECTED-QROOT-PAPER-Q-SUM
source: the actual `InitialThetaData` section, its q-root/Tate-family order
identity, `AdelicThetaLinkData.ofInitialThetaOddTateSection`, and Joshi–Teich,
*Arithmetic Teichmuller Spaces III*, `th:moccor-Mochizuki-form2` and
`cor:cor312`.
fidelity: identifies the finite selected q-root source subtype with the
canonical section-link places and transports the paper-normalized local q-order
sum, grouped by residue characteristic. It concerns the link built from the
same `InitialThetaData`; an independently supplied Scene1 link remains open.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-- The selected q-root source has exactly one index for each place of the
canonical link built from the same initial theta section. -/
noncomputable def iutInitialThetaOddSupportSelectedQRootSourcePlaces_sectionLinkEquiv
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} ≃
    {w : NumberField.FinitePlace ↥D.prime.torsionField //
      w ∈ (AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
        packetHull heightData ramification logVolume processionLength).places} := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
    packetHull heightData ramification logVolume processionLength
  let S := {s : R.badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
  have hImage :
      (fun s : R.badFinset => s.1) ''
          iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
        (↑L.places : Set (NumberField.FinitePlace ↥D.prime.torsionField)) := by
    simpa [R, L] using
      iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionLinkPlaces
        D theta thetaBase packetHull heightData ramification logVolume processionLength
  let f : S → W := fun s =>
    ⟨s.1.1, by
      have hs : s.1.1 ∈ (fun t : R.badFinset => t.1) ''
          iutInitialThetaOddSupportSelectedQRootSourcePlaces D :=
        ⟨s.1, s.2, rfl⟩
      rw [hImage] at hs
      exact hs⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro s t hst
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : W => w.1) hst
  · intro w
    have hw : w.1 ∈ (fun s : R.badFinset => s.1) ''
        iutInitialThetaOddSupportSelectedQRootSourcePlaces D := by
      rw [hImage]
      exact w.2
    rcases hw with ⟨s, hs, hsw⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    exact hsw

private theorem iutInitialThetaOddSupportSelectedQRootSourcePlace_ramIdx_mul_ordp_eq_sectionLinkQOrder
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D})
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    (Arithmetic.ramIdx s.1.1 : ℝ) *
        Arithmetic.ordp s.1.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1) =
      ((AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
        packetHull heightData ramification logVolume processionLength).tate.qOrder
          s.1.1 : ℝ) /
        (2 * (D.prime.ℓ : ℝ)) := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
    packetHull heightData ramification logVolume processionLength
  let T := iutInitialThetaOddTateSectionTateParameterData D
  rcases s with ⟨sVal, hs⟩
  rcases hs with ⟨v, hv, hsection⟩
  let selected := iutInitialThetaOddSupportSelectedQRootPlace D v hv
  have hSelectedPlace : selected = sVal :=
    Subtype.ext hsection
  subst sVal
  let w := selected.1
  have hSelected : w ∈ iutInitialThetaOddSupportSelectedQRootPlaces D :=
    ⟨v, hv, rfl⟩
  let sectionTate := iutInitialThetaOddTateSectionTateStructure D w hSelected
  let familyBad := iutInitialThetaOddSupportTateFamily_badPlace_source D selected
  let familyTate := (iutInitialThetaTateFamilyOfTorsion D).S w familyBad
  have hLocal :
      (Arithmetic.ramIdx w : ℝ) * Arithmetic.ordp w (R.qroot selected) =
        (iutCompletionQOrder w familyTate.t.q : ℝ) /
          (2 * (D.prime.ℓ : ℝ)) := by
    simpa [R, familyTate, familyBad] using
      iutInitialThetaOddSupportSelectedQRootPlace_ramIdx_mul_ordp_eq_sectionQOrder
        D v hv
  have hSameTate : familyTate.t = sectionTate.t := by
    apply TateParameter.tateJ_injective _ _
      (JoshiTeich.ReferenceIut.twelve_ne_zero w)
    have hJ₁ := iutTateStructure_tateJ_eq familyTate
    have hJ₂ := iutTateStructure_tateJ_eq sectionTate
    exact hJ₁.trans hJ₂.symm
  have hSectionParameter :=
    iutInitialThetaOddTateSectionTateParameterData_parameter_eq D w hSelected
  have hParameter : T.parameter w = familyTate.t.q := by
    calc
      T.parameter w = sectionTate.t.q := hSectionParameter
      _ = familyTate.t.q := by
        exact congrArg (fun t : TateParameter
          (w.maximalIdeal.adicCompletion (↥D.prime.torsionField)) =>
            (t.q : w.maximalIdeal.adicCompletion (↥D.prime.torsionField)))
          hSameTate.symm
  have hLinkParameter : L.tate.parameter w = T.parameter w := by
    rfl
  have hOrder : L.tate.qOrder w = iutCompletionQOrder w familyTate.t.q := by
    change Arithmetic.completionQOrder w (L.tate.parameter w) =
      Arithmetic.completionQOrder w familyTate.t.q
    exact congrArg (Arithmetic.completionQOrder w)
      (hLinkParameter.trans hParameter)
  rw [hOrder]
  exact hLocal

/-- The section-selected q-root sum is the paper-normalized q-order sum on
the places of its canonical link, grouped by residue characteristic. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_paperQLogSum_eq_sectionLink
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
      packetHull heightData ramification logVolume processionLength
    let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
    letI : Fintype W := Fintype.ofFinset L.places (fun _ => Iff.rfl)
    let P := (Finset.univ : Finset W).image (fun w => Arithmetic.residueChar w.1)
    ∑ p ∈ P,
      ∑ s ∈ (Finset.univ : Finset S).filter
        (fun s => Arithmetic.residueChar s.1.1 = p),
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
          Real.log p =
    ∑ p ∈ P,
      ∑ w ∈ (Finset.univ : Finset W).filter
        (fun w => Arithmetic.residueChar w.1 = p),
        (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log p) := by
  classical
  let L := AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
    packetHull heightData ramification logVolume processionLength
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let W := {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ L.places}
  letI : Fintype W := Fintype.ofFinset L.places (fun _ => Iff.rfl)
  let P := (Finset.univ : Finset W).image (fun w => Arithmetic.residueChar w.1)
  let e := iutInitialThetaOddSupportSelectedQRootSourcePlaces_sectionLinkEquiv
    D theta thetaBase packetHull heightData ramification logVolume processionLength
  have hFiber (p : ℕ) :
      (∑ s : S,
        if Arithmetic.residueChar s.1.1 = p then
          ((Arithmetic.ramIdx s.1.1 : ℝ) *
            Arithmetic.ordp s.1.1 (R.qroot s.1)) * Real.log p
        else 0) =
      ∑ w : W,
        if Arithmetic.residueChar w.1 = p then
          (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) * Real.log p)
        else 0 := by
    calc
      _ = ∑ s : S,
          if Arithmetic.residueChar (e s).1 = p then
            (((L.tate.qOrder (e s).1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
              Real.log p)
          else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        have hTerm :=
          iutInitialThetaOddSupportSelectedQRootSourcePlace_ramIdx_mul_ordp_eq_sectionLinkQOrder
            D s theta thetaBase packetHull heightData ramification logVolume processionLength
        rw [hTerm, (show (e s).1 = s.1.1 from rfl).symm]
      _ = ∑ w : W,
          if Arithmetic.residueChar w.1 = p then
            (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
              Real.log p)
          else 0 := by
        simpa using e.sum_comp (fun w =>
          if Arithmetic.residueChar w.1 = p then
            (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
              Real.log p)
          else 0)
  calc
    (∑ p ∈ P,
      ∑ s ∈ (Finset.univ : Finset S).filter
        (fun s => Arithmetic.residueChar s.1.1 = p),
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1 (R.qroot s.1)) * Real.log p) =
      ∑ p ∈ P, ∑ s : S,
        if Arithmetic.residueChar s.1.1 = p then
          ((Arithmetic.ramIdx s.1.1 : ℝ) *
            Arithmetic.ordp s.1.1 (R.qroot s.1)) * Real.log p
        else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ w : W,
        if Arithmetic.residueChar w.1 = p then
          (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
            Real.log p)
        else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hFiber p
    _ = ∑ p ∈ P,
      ∑ w ∈ (Finset.univ : Finset W).filter
        (fun w => Arithmetic.residueChar w.1 = p),
        (((L.tate.qOrder w.1 : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_filter]

end

end JoshiTeich.Act1Scene1
