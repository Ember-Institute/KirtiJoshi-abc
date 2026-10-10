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

end

end JoshiTeich.Act1Scene1
