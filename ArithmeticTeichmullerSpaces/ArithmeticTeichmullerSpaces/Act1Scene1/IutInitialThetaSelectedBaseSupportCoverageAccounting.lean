import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedBaseSupportCoverage
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRootAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField
open WithZero
open scoped BigOperators Classical NumberField Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-SELECTED-SUPPORT-COVERAGE-ACCOUNTING
source: the coverage equivalence in
`IutInitialThetaSelectedBaseSupportCoverage.lean`, the selected section
q-root fibre identity in `IutInitialThetaSelectedQRootAccounting.lean`, and
the full-support weighted q-root accounting in
`IutInitialThetaOddSupportQRootAccounting.lean`.
fidelity: under the explicit section-coverage condition, identifies the
selected section fibre with the complete odd-support torsion q-root fibre.
The condition remains an input; this theorem does not prove it from
`InitialThetaData`.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-! The selected section fibre and the complete odd-support fibre have the
same q-pilot weighted value once the section covers every base support place. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_fiber_eq_fullSupport
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ)
    (hCoverage : ∀ w : NumberField.FinitePlace D.F,
      w ∈ IutOddMultiplicativeSupport D →
        iutInitialThetaSectionBasePlace D
            (iutPlaceUnder (F :=
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
              (Kt := D.F) w) = w) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S :=
      {s : R.badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    ∑ s : S,
        (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
              Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1)))
        else 0) =
      IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let S :=
    {s : R.badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let T :=
    {b : NumberField.FinitePlace D.F //
      b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
  letI : Fintype T :=
    (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
  have hSupport :
      iutInitialThetaOddSupportSelectedBasePlaces D =
        IutOddMultiplicativeSupport D :=
    (iutInitialThetaOddSupportSelectedBasePlaces_eq_fullSupport_iff D).mpr
      hCoverage
  let e : T ≃ B.badFinset :=
    { toFun := fun b =>
        ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr (by
          have hbSupport : b.1 ∈ IutOddMultiplicativeSupport D := by
            simpa [hSupport] using b.2
          change b.1 ∈ IutOddMultiplicativeSupport D
          exact hbSupport)⟩
      invFun := fun w =>
        ⟨w.1, by
          have hwSupport : w.1 ∈ IutOddMultiplicativeSupport D := by
            have hwB := (Set.ext_iff.mp B.badFinset_spec w.1).mp w.2
            change w.1 ∈ IutOddMultiplicativeSupport D at hwB
            exact hwB
          simpa [hSupport] using hwSupport⟩
      left_inv := by
        intro b
        rfl
      right_inv := by
        intro w
        rfl }
  let f : T → ℝ := fun b =>
    if Arithmetic.residueChar b.1 = p then
      Arithmetic.qPilotWeight b.1 *
        (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
          (2 * (D.prime.ℓ : ℝ))
    else 0
  let g : B.badFinset → ℝ := fun w =>
    if Arithmetic.residueChar w.1 = p then
      Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
        (2 * (D.prime.ℓ : ℝ))
    else 0
  have hSelected :=
    iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_baseRamIdx_mul_ordp_fiber_eq
      D p
  have hBase : (∑ b : T, f b) = ∑ w : B.badFinset, g w := by
    calc
      (∑ b : T, f b) = ∑ b : T, g (e b) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hq :
            iutInitialThetaOddSupportSelectedBaseQOrder D b =
              B.qOrder (e b) := by
          apply congrArg B.qOrder
          apply Subtype.ext
          rfl
        simp only [f, g]
        rw [hq]
        have he : (e b).1 = b.1 := rfl
        rw [he]
      _ = ∑ w : B.badFinset, g w := by
        simpa using e.sum_comp g
  have hAttach :
      (∑ w : B.badFinset, g w) =
        ∑ w ∈ B.badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
          Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
    change (∑ w : B.badFinset,
      if Arithmetic.residueChar w.1 = p then
        Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
          (2 * (D.prime.ℓ : ℝ))
      else 0) = _
    have hSubtype :
        (∑ w : B.badFinset, g w) =
          ∑ w ∈ B.badFinset.attach,
            (if Arithmetic.residueChar w.1 = p then
              Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
                (2 * (D.prime.ℓ : ℝ))
            else 0) := by
      refine Finset.sum_bij (fun w _ => w) ?_ ?_ ?_ ?_
      · intro w hw
        simp
      · intro w₁ hw₁ w₂ hw₂ h
        exact h
      · intro w hw
        exact ⟨w, Finset.mem_univ _, rfl⟩
      · intro w hw
        rfl
    calc
      (∑ w : B.badFinset, g w) =
          ∑ w ∈ B.badFinset.attach,
            (if Arithmetic.residueChar w.1 = p then
              Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
                (2 * (D.prime.ℓ : ℝ))
            else 0) := hSubtype
      _ = _ := by
        rw [Finset.sum_filter]
  calc
    (∑ s : S,
        (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
              Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))
        else 0)) = (∑ b : T, f b) := by
      simpa [f, R, S, T] using hSelected
    _ = ∑ w : B.badFinset, g w := hBase
    _ = ∑ w ∈ B.badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
          Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := hAttach
    _ = IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
      symm
      exact IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder D p

/-! The fibre bridge can be assembled into the logarithmic finite sum on the
selected residue-characteristic image.  The image is kept explicit so that
coverage is not silently promoted to a global support identification. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_logSum_eq_fullSupport_on_selectedResidueImage
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hCoverage : ∀ w : NumberField.FinitePlace D.F,
      w ∈ IutOddMultiplicativeSupport D →
        iutInitialThetaSectionBasePlace D
            (iutPlaceUnder (F :=
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
              (Kt := D.F) w) = w) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S :=
      {s : R.badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    let P := (Finset.univ : Finset S).image
      (fun s => Arithmetic.residueChar (R.basePlace s.1).1)
    ∑ p ∈ P,
        Real.log p *
          ∑ s ∈ (Finset.univ : Finset S).filter
            (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
            Arithmetic.qPilotWeight (R.basePlace s.1).1 *
              ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                Arithmetic.ordp s.1.1
                  (R.qroot (show R.badFinset from s.1))) =
      ∑ p ∈ P,
        Real.log p *
          IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S :=
    {s : R.badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let P := (Finset.univ : Finset S).image
    (fun s => Arithmetic.residueChar (R.basePlace s.1).1)
  have hFiber (p : ℕ) :
      (∑ s : S,
        if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
              Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))
        else 0) =
      ∑ s ∈ (Finset.univ : Finset S).filter
        (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
        Arithmetic.qPilotWeight (R.basePlace s.1).1 *
          ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1))) := by
    rw [Finset.sum_filter]
  have hSelected (p : ℕ) :
      (∑ s : S,
        if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
              Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))
        else 0) =
      IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
    simpa [R, S] using
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_fiber_eq_fullSupport
        D p hCoverage)
  calc
    (∑ p ∈ P,
        Real.log p *
          ∑ s ∈ (Finset.univ : Finset S).filter
            (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
            Arithmetic.qPilotWeight (R.basePlace s.1).1 *
              ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                Arithmetic.ordp s.1.1
                  (R.qroot (show R.badFinset from s.1)))) =
      ∑ p ∈ P,
        Real.log p *
          ∑ s : S,
            if Arithmetic.residueChar (R.basePlace s.1).1 = p then
              Arithmetic.qPilotWeight (R.basePlace s.1).1 *
                ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                  Arithmetic.ordp s.1.1
                    (R.qroot (show R.badFinset from s.1)))
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hFiber p]
    _ = ∑ p ∈ P,
        Real.log p *
          IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hSelected p]

/-! Under coverage, the finite prime image used by the selected source is the
same image as the full base q-pilot support. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_residueCharImage_eq_fullSupport
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hCoverage : ∀ w : NumberField.FinitePlace D.F,
      w ∈ IutOddMultiplicativeSupport D →
        iutInitialThetaSectionBasePlace D
            (iutPlaceUnder (F :=
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
              (Kt := D.F) w) = w) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S :=
      {s : R.badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    let P := (Finset.univ : Finset S).image
      (fun s => Arithmetic.residueChar (R.basePlace s.1).1)
    let Q := (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.image
      Arithmetic.residueChar
    P = Q := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let S :=
    {s : R.badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let T :=
    {b : NumberField.FinitePlace D.F //
      b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
  letI : Fintype T :=
    (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
  have hSupport :
      iutInitialThetaOddSupportSelectedBasePlaces D =
        IutOddMultiplicativeSupport D :=
    (iutInitialThetaOddSupportSelectedBasePlaces_eq_fullSupport_iff D).mpr
      hCoverage
  let eBase : S ≃ T :=
    iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  let eFull : T ≃ B.badFinset :=
    { toFun := fun b =>
        ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr (by
          have hbSupport : b.1 ∈ IutOddMultiplicativeSupport D := by
            simpa [hSupport] using b.2
          change b.1 ∈ IutOddMultiplicativeSupport D
          exact hbSupport)⟩
      invFun := fun w =>
        ⟨w.1, by
          have hwSupport : w.1 ∈ IutOddMultiplicativeSupport D := by
            have hwB := (Set.ext_iff.mp B.badFinset_spec w.1).mp w.2
            change w.1 ∈ IutOddMultiplicativeSupport D at hwB
            exact hwB
          simpa [hSupport] using hwSupport⟩
      left_inv := by
        intro b
        rfl
      right_inv := by
        intro w
        rfl }
  let P := (Finset.univ : Finset S).image
    (fun s => Arithmetic.residueChar (R.basePlace s.1).1)
  let Q := B.badFinset.image Arithmetic.residueChar
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨s, hs, hsp⟩
    let b : T := eBase s
    let w : B.badFinset := eFull b
    refine Finset.mem_image.mpr ⟨w.1, w.2, ?_⟩
    have hbase : (eBase s).1 = (R.basePlace s.1).1 := by
      apply Subtype.ext
      rfl
    have hfull : (eFull (eBase s)).1 = (eBase s).1 := by
      rfl
    change Arithmetic.residueChar (eFull (eBase s)).1 = p
    rw [hfull, hbase]
    exact hsp
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨w, hw, hwp⟩
    let b : T := eFull.symm ⟨w, hw⟩
    let s : S := eBase.symm b
    refine Finset.mem_image.mpr ⟨s, Finset.mem_univ _, ?_⟩
    have hbs : eBase s = b := by
      exact eBase.apply_symm_apply b
    have hbw : eFull b = ⟨w, hw⟩ := by
      exact eFull.apply_symm_apply ⟨w, hw⟩
    have hbase : (R.basePlace s.1).1 = w := by
      calc
        (R.basePlace s.1).1 = (eBase s).1 := by rfl
        _ = b.1 := congrArg Subtype.val hbs
        _ = (eFull b).1 := by rfl
        _ = w := congrArg Subtype.val hbw
    rw [hbase]
    exact hwp

/-! The full odd-support fibre identity itself has an unconditional global
logarithmic presentation over the finite support image. -/
theorem iutInitialThetaOddSupportWeighted_logSum_eq_baseQOrder_on_fullResidueImage
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    let Q := B.badFinset.image Arithmetic.residueChar
    ∑ p ∈ Q,
        Real.log p *
          IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
      ∑ p ∈ Q,
        Real.log p *
          ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
            Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
              (2 * (D.prime.ℓ : ℝ)) := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let Q := B.badFinset.image Arithmetic.residueChar
  have hFiber (p : ℕ) :
      IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
        ∑ w ∈ B.badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
          Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
    simpa [B] using
      (IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder D p)
  apply Finset.sum_congr rfl
  intro p hp
  rw [hFiber p]

/-! Combining the image equality with the preceding global identity transports
the selected q-root log sum to the full-support base q-order sum. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_logSum_eq_baseQOrder_on_fullResidueImage
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hCoverage : ∀ w : NumberField.FinitePlace D.F,
      w ∈ IutOddMultiplicativeSupport D →
        iutInitialThetaSectionBasePlace D
            (iutPlaceUnder (F :=
              ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
              (Kt := D.F) w) = w) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let S :=
      {s : R.badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    let Q := B.badFinset.image Arithmetic.residueChar
    ∑ p ∈ Q,
        Real.log p *
          ∑ s ∈ (Finset.univ : Finset S).filter
            (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
            Arithmetic.qPilotWeight (R.basePlace s.1).1 *
              ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                Arithmetic.ordp s.1.1
                  (R.qroot (show R.badFinset from s.1))) =
      ∑ p ∈ Q,
        Real.log p *
          ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
            Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
              (2 * (D.prime.ℓ : ℝ)) := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S :=
    {s : R.badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let P := (Finset.univ : Finset S).image
    (fun s => Arithmetic.residueChar (R.basePlace s.1).1)
  let Q := B.badFinset.image Arithmetic.residueChar
  have hImage : P = Q := by
    simpa [R, S, B, P, Q] using
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_residueCharImage_eq_fullSupport
        D hCoverage)
  have hSelected :
      (∑ p ∈ P,
        Real.log p *
          ∑ s ∈ (Finset.univ : Finset S).filter
            (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
            Arithmetic.qPilotWeight (R.basePlace s.1).1 *
              ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                Arithmetic.ordp s.1.1
                  (R.qroot (show R.badFinset from s.1)))) =
        ∑ p ∈ P,
          Real.log p *
            IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
    simpa [R, S, P] using
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_logSum_eq_fullSupport_on_selectedResidueImage
        D hCoverage)
  have hFull :
      (∑ p ∈ Q,
        Real.log p *
          IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p) =
        ∑ p ∈ Q,
          Real.log p *
            ∑ w ∈ B.badFinset.attach.filter
              (fun w => Arithmetic.residueChar w.1 = p),
              Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
                (2 * (D.prime.ℓ : ℝ)) := by
    simpa [B, Q] using
      (iutInitialThetaOddSupportWeighted_logSum_eq_baseQOrder_on_fullResidueImage D)
  rw [hImage] at hSelected
  calc
    (∑ p ∈ Q,
        Real.log p *
          ∑ s ∈ (Finset.univ : Finset S).filter
            (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
            Arithmetic.qPilotWeight (R.basePlace s.1).1 *
              ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                Arithmetic.ordp s.1.1
                  (R.qroot (show R.badFinset from s.1)))) =
      ∑ p ∈ Q,
        Real.log p *
          IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p := by
      exact hSelected
    _ = ∑ p ∈ Q,
        Real.log p *
          ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
            Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
              (2 * (D.prime.ℓ : ℝ)) := by
      exact hFull

end

end JoshiTeich.Act1Scene1
