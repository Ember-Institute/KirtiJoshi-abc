import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRoot

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField
open WithZero
open scoped BigOperators Classical NumberField Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-SELECTED-QROOT-WEIGHTED-ACCOUNTING
source: `iut`: the finite-place q-root valuation accounting from
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean` and `Ordp.lean`,
combined with the actual section representative and contraction interfaces
ported from `ThetaData/LocalConditions.lean` and `ThetaData/PlaceUnder.lean`.
fidelity: on the finite selected section carrier, the q-pilot residue-degree
weight is transported across the proved source/base-place equivalence. The
local identity `baseRamIdx * ordp(qroot) = qOrder/(2*ell)` is used to obtain the
selected base q-order sum. This does not identify the carrier with the paper's
`L'` representatives or `underline V^oss`, and it does not remove the
q-pilot weight or prove the unweighted paper sum.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-- The q-pilot weight of a selected contracted base place, viewed as an index
of the base q-pilot source. -/
noncomputable def iutInitialThetaOddSupportSelectedBaseQOrder
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (b : {b : NumberField.FinitePlace D.F //
      b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}) : ℕ :=
  (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
    ⟨b.1, (Set.ext_iff.mp
      (iutInitialThetaOddSupportBaseQPilotSource D).badFinset_spec b.1).mpr
      (iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D b.2)⟩

/-! The selected source subtype has the same underlying place image as the
section's formal `underline V^oss` carrier. This is the source-level form of
the already proved equality for selected q-root places. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionVoss
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset => s.1) ''
        iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
      iutInitialThetaSectionVoss D := by
  calc
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset => s.1) ''
          iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
        iutInitialThetaOddSupportSelectedQRootPlaces D := by
      ext w
      constructor
      · rintro ⟨s, hs, rfl⟩
        simpa [iutInitialThetaOddSupportSelectedQRootSourcePlaces] using hs
      · intro hw
        rcases hw with ⟨v, hv, rfl⟩
        exact ⟨iutInitialThetaOddSupportSelectedQRootPlace D v hv,
          ⟨v, hv, rfl⟩, rfl⟩
    _ = iutInitialThetaOddTateSectionPlaces D :=
      iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces D
    _ = iutInitialThetaSectionVoss D :=
      iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D

theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_baseRamIdx_mul_ordp_sum_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
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
    ∑ s : S,
        Arithmetic.qPilotWeight (R.basePlace s.1).1 *
          ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1))) =
      ∑ b : T,
        Arithmetic.qPilotWeight b.1 *
          (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
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
  let e := iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  let bIndex : T → B.badFinset := fun b =>
    ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr
      (iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D b.2)⟩
  have hIndex (b : T) :
      iutInitialThetaOddSupportSelectedBaseQOrder D b = B.qOrder (bIndex b) := by
    rfl
  have hBase (s : S) :
      bIndex (e s) = R.basePlace s.1 := by
    apply Subtype.ext
    rfl
  have hLocal (s : S) :
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
        (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
    rcases s.2 with ⟨v, hv, hsection⟩
    have hs : iutInitialThetaOddSupportSelectedQRootPlace D v hv = s.1 :=
      Subtype.ext hsection
    have h := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder
      D v hv
    have hbase :
        R.basePlace s.1 =
          R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv) := by
      rw [hs]
    have hbase' :
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          B.qOrder (bIndex (e s)) := by
      calc
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
            B.qOrder (R.basePlace s.1) := by rw [hs]
        _ = B.qOrder (bIndex (e s)) := by rw [hBase s]
    have h' :
        Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          (B.qOrder
              (R.basePlace
                (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ) *
              Arithmetic.ramIdx
                (R.basePlace
                  (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := by
      simpa [R, B] using h
    calc
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
          Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) := by
        rw [hs]
      _ = (B.qOrder
            (R.basePlace
              (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ) *
              Arithmetic.ramIdx
                (R.basePlace
                  (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := h'
      _ = (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
        rw [hbase', ← hbase]
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have hRam (s : S) :
      (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos (R.basePlace s.1).1).ne'
  calc
    (∑ s : S,
        Arithmetic.qPilotWeight (R.basePlace s.1).1 *
          ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))) =
        ∑ s : S,
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((B.qOrder (bIndex (e s)) : ℝ) /
              (2 * (D.prime.ℓ : ℝ))) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hLocal s]
      have hram := hRam s
      field_simp [hram, hEll]
    _ = ∑ s : S,
          Arithmetic.qPilotWeight (bIndex (e s)).1 *
            ((B.qOrder (bIndex (e s)) : ℝ) /
              (2 * (D.prime.ℓ : ℝ))) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hBase s]
    _ = ∑ b : T,
          Arithmetic.qPilotWeight (bIndex b).1 *
            ((B.qOrder (bIndex b) : ℝ) /
              (2 * (D.prime.ℓ : ℝ))) := by
      simpa using e.sum_comp (fun b =>
        Arithmetic.qPilotWeight (bIndex b).1 *
          ((B.qOrder (bIndex b) : ℝ) /
            (2 * (D.prime.ℓ : ℝ))) )
    _ = ∑ b : T,
          Arithmetic.qPilotWeight b.1 *
            (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
              (2 * (D.prime.ℓ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbIndex : (bIndex b).1 = b.1 := by
        rfl
      rw [hbIndex, hIndex b]
      ring

end

/-! Removing the q-pilot coefficient leaves the representative multiplicity
accounting itself.  The equality below is still on the actual section-selected
carrier; it does not identify that carrier with the paper's independently
chosen `L'` representatives. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_baseRamIdx_mul_ordp_sum_eq_unweighted
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
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
    ∑ s : S,
        (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
          Arithmetic.ordp s.1.1
            (R.qroot (show R.badFinset from s.1)) =
      ∑ b : T,
        (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
          (2 * (D.prime.ℓ : ℝ)) := by
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
  let e := iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  let bIndex : T → B.badFinset := fun b =>
    ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr
      (iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D b.2)⟩
  have hIndex (b : T) :
      iutInitialThetaOddSupportSelectedBaseQOrder D b = B.qOrder (bIndex b) := by
    rfl
  have hBase (s : S) :
      bIndex (e s) = R.basePlace s.1 := by
    apply Subtype.ext
    rfl
  have hLocal (s : S) :
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
        (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
    rcases s.2 with ⟨v, hv, hsection⟩
    have hs : iutInitialThetaOddSupportSelectedQRootPlace D v hv = s.1 :=
      Subtype.ext hsection
    have h := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder
      D v hv
    have hbase :
        R.basePlace s.1 =
          R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv) := by
      rw [hs]
    have hbase' :
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          B.qOrder (bIndex (e s)) := by
      calc
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
            B.qOrder (R.basePlace s.1) := by rw [hs]
        _ = B.qOrder (bIndex (e s)) := by rw [hBase s]
    have h' :
        Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          (B.qOrder
              (R.basePlace
                (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ) *
              Arithmetic.ramIdx
                (R.basePlace
                  (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := by
      simpa [R, B] using h
    calc
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
          Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) := by
        rw [hs]
      _ = (B.qOrder
            (R.basePlace
              (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ) *
              Arithmetic.ramIdx
                (R.basePlace
                  (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := h'
      _ = (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
        rw [hbase', ← hbase]
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have hRam (s : S) :
      (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos (R.basePlace s.1).1).ne'
  have hTerm (s : S) :
      (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
          Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
        (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ)) := by
    rw [hLocal s]
    field_simp [hRam s, hEll]
  calc
    (∑ s : S,
        (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
          Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1))) =
        ∑ s : S,
          (B.qOrder (bIndex (e s)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hTerm s
    _ = ∑ b : T,
          (B.qOrder (bIndex b) : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
      simpa using e.sum_comp (fun b =>
        (B.qOrder (bIndex b) : ℝ) /
          (2 * (D.prime.ℓ : ℝ)))
    _ = ∑ b : T,
          (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hIndex b]

/-! The same accounting can be restricted to one residue characteristic.
The restriction is the finite-fibre interface needed before comparing the
selected carrier with the paper's `(p,w)` indexing. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_baseRamIdx_mul_ordp_fiber_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
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
    ∑ s : S,
        (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
              Arithmetic.ordp s.1.1
                (R.qroot (show R.badFinset from s.1)))
        else 0) =
      ∑ b : T,
        (if Arithmetic.residueChar b.1 = p then
          Arithmetic.qPilotWeight b.1 *
            (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
              (2 * (D.prime.ℓ : ℝ))
        else 0) := by
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
  let e := iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  let bIndex : T → B.badFinset := fun b =>
    ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr
      (iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D b.2)⟩
  have hIndex (b : T) :
      iutInitialThetaOddSupportSelectedBaseQOrder D b = B.qOrder (bIndex b) := by
    rfl
  have hBase (s : S) :
      bIndex (e s) = R.basePlace s.1 := by
    apply Subtype.ext
    rfl
  have hLocal (s : S) :
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
        (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
    rcases s.2 with ⟨v, hv, hsection⟩
    have hs : iutInitialThetaOddSupportSelectedQRootPlace D v hv = s.1 :=
      Subtype.ext hsection
    have h := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder
      D v hv
    have hbase :
        R.basePlace s.1 =
          R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv) := by
      rw [hs]
    have hbase' :
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          B.qOrder (bIndex (e s)) := by
      calc
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
            B.qOrder (R.basePlace s.1) := by rw [hs]
        _ = B.qOrder (bIndex (e s)) := by rw [hBase s]
    have h' :
        Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          (B.qOrder
              (R.basePlace
                (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ) *
              Arithmetic.ramIdx
                (R.basePlace
                  (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := by
      simpa [R, B] using h
    calc
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
          Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) := by
        rw [hs]
      _ = (B.qOrder
            (R.basePlace
              (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx
              (R.basePlace
                (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := h'
      _ = (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
        rw [hbase', ← hbase]
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have hRam (s : S) :
      (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos (R.basePlace s.1).1).ne'
  have hTerm (s : S) :
      Arithmetic.qPilotWeight (R.basePlace s.1).1 *
          ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1))) =
        Arithmetic.qPilotWeight (bIndex (e s)).1 *
          ((B.qOrder (bIndex (e s)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ))) := by
    have hram' :
        (Arithmetic.ramIdx (bIndex (e s)).1 : ℝ) ≠ 0 := by
      rw [hBase s]
      exact hRam s
    rw [hLocal s]
    rw [← hBase s]
    field_simp [hram', hEll]
  calc
    (∑ s : S,
        (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          Arithmetic.qPilotWeight (R.basePlace s.1).1 *
            ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
              Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)))
        else 0)) =
        ∑ s : S,
          (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
            Arithmetic.qPilotWeight (bIndex (e s)).1 *
              ((B.qOrder (bIndex (e s)) : ℝ) /
                (2 * (D.prime.ℓ : ℝ)))
          else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hp : Arithmetic.residueChar (R.basePlace s.1).1 = p
      · simp only [if_pos hp]
        exact hTerm s
      · simp only [if_neg hp]
    _ = ∑ s : S,
          (if Arithmetic.residueChar (bIndex (e s)).1 = p then
            Arithmetic.qPilotWeight (bIndex (e s)).1 *
              ((B.qOrder (bIndex (e s)) : ℝ) /
                (2 * (D.prime.ℓ : ℝ)))
          else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hBase s]
    _ = ∑ b : T,
          (if Arithmetic.residueChar (bIndex b).1 = p then
            Arithmetic.qPilotWeight (bIndex b).1 *
              ((B.qOrder (bIndex b) : ℝ) /
                (2 * (D.prime.ℓ : ℝ)))
          else 0) := by
      simpa using e.sum_comp (fun b =>
        if Arithmetic.residueChar (bIndex b).1 = p then
          Arithmetic.qPilotWeight (bIndex b).1 *
            ((B.qOrder (bIndex b) : ℝ) /
              (2 * (D.prime.ℓ : ℝ)))
        else 0)
    _ = ∑ b : T,
          (if Arithmetic.residueChar b.1 = p then
            Arithmetic.qPilotWeight b.1 *
              (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
                (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbIndex : (bIndex b).1 = b.1 := by rfl
      by_cases hp : Arithmetic.residueChar b.1 = p
      · rw [hbIndex, hIndex b]
        simp only [if_pos hp]
        ring
      · rw [hbIndex, hIndex b]
        simp only [if_neg hp]

/-! Removing the q-pilot coefficient commutes with the same residue-characteristic
fibre restriction.  This is the unweighted `(p,w)` index interface for the
selected section carrier. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_baseRamIdx_mul_ordp_fiber_eq_unweighted
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
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
    ∑ s : S,
        (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1))
        else 0) =
      ∑ b : T,
        (if Arithmetic.residueChar b.1 = p then
          (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
            (2 * (D.prime.ℓ : ℝ))
        else 0) := by
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
  let e := iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  let bIndex : T → B.badFinset := fun b =>
    ⟨b.1, (Set.ext_iff.mp B.badFinset_spec b.1).mpr
      (iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D b.2)⟩
  have hIndex (b : T) :
      iutInitialThetaOddSupportSelectedBaseQOrder D b = B.qOrder (bIndex b) := by
    rfl
  have hBase (s : S) :
      bIndex (e s) = R.basePlace s.1 := by
    apply Subtype.ext
    rfl
  have hLocal (s : S) :
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
        (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
    rcases s.2 with ⟨v, hv, hsection⟩
    have hs : iutInitialThetaOddSupportSelectedQRootPlace D v hv = s.1 :=
      Subtype.ext hsection
    have h := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder
      D v hv
    have hbase :
        R.basePlace s.1 =
          R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv) := by
      rw [hs]
    have hbase' :
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          B.qOrder (bIndex (e s)) := by
      calc
        B.qOrder (R.basePlace (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
            B.qOrder (R.basePlace s.1) := by rw [hs]
        _ = B.qOrder (bIndex (e s)) := by rw [hBase s]
    have h' :
        Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) =
          (B.qOrder
              (R.basePlace
                (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
            (2 * (D.prime.ℓ : ℝ) *
              Arithmetic.ramIdx
                (R.basePlace
                  (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := by
      simpa [R, B] using h
    calc
      Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
          Arithmetic.ordp
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1
            (R.qroot (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) := by
        rw [hs]
      _ = (B.qOrder
            (R.basePlace
              (iutInitialThetaOddSupportSelectedQRootPlace D v hv)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx
              (R.basePlace
                (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1) := h'
      _ = (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) *
            Arithmetic.ramIdx (R.basePlace s.1).1) := by
        rw [hbase', ← hbase]
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have hRam (s : S) :
      (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos (R.basePlace s.1).1).ne'
  have hTerm (s : S) :
      (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
          Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1)) =
        (B.qOrder (bIndex (e s)) : ℝ) /
          (2 * (D.prime.ℓ : ℝ)) := by
    have hram' :
        (Arithmetic.ramIdx (bIndex (e s)).1 : ℝ) ≠ 0 := by
      rw [hBase s]
      exact hRam s
    rw [hLocal s]
    rw [← hBase s]
    field_simp [hram', hEll]
  calc
    (∑ s : S,
        (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1 (R.qroot (show R.badFinset from s.1))
        else 0)) =
        ∑ s : S,
          (if Arithmetic.residueChar (R.basePlace s.1).1 = p then
            (B.qOrder (bIndex (e s)) : ℝ) /
              (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hp : Arithmetic.residueChar (R.basePlace s.1).1 = p
      · simp only [if_pos hp]
        exact hTerm s
      · simp only [if_neg hp]
    _ = ∑ s : S,
          (if Arithmetic.residueChar (bIndex (e s)).1 = p then
            (B.qOrder (bIndex (e s)) : ℝ) /
              (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hBase s]
    _ = ∑ b : T,
          (if Arithmetic.residueChar (bIndex b).1 = p then
            (B.qOrder (bIndex b) : ℝ) /
              (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      simpa using e.sum_comp (fun b =>
        if Arithmetic.residueChar (bIndex b).1 = p then
          (B.qOrder (bIndex b) : ℝ) /
            (2 * (D.prime.ℓ : ℝ))
        else 0)
    _ = ∑ b : T,
          (if Arithmetic.residueChar b.1 = p then
            (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
              (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbIndex : (bIndex b).1 = b.1 := by rfl
      by_cases hp : Arithmetic.residueChar b.1 = p
      · rw [hbIndex, hIndex b]
      · rw [hbIndex, hIndex b]

/-! The per-characteristic identities can be assembled over the finite image of
the selected base-place carrier.  This is the explicit grouped `(p,w)` form;
the carrier is still the actual section-selected one. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_baseRamIdx_mul_ordp_sum_eq_unweighted_residueChar_grouped
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
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
    let P :=
      (Finset.univ : Finset T).image (fun b => Arithmetic.residueChar b.1)
    ∑ p ∈ P,
        ∑ s ∈ (Finset.univ : Finset S).filter
          (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
          (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1)) =
      ∑ p ∈ P,
        ∑ b ∈ (Finset.univ : Finset T).filter
          (fun b => Arithmetic.residueChar b.1 = p),
          (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
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
  let P :=
    (Finset.univ : Finset T).image (fun b => Arithmetic.residueChar b.1)
  have hFiber (p : ℕ) :
      (∑ s : S,
        if Arithmetic.residueChar (R.basePlace s.1).1 = p then
          (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1))
        else 0) =
      ∑ b : T,
        if Arithmetic.residueChar b.1 = p then
          (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
            (2 * (D.prime.ℓ : ℝ))
        else 0 := by
    simpa [R, S, T] using
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_baseRamIdx_mul_ordp_fiber_eq_unweighted
        D p)
  calc
    (∑ p ∈ P,
        ∑ s ∈ (Finset.univ : Finset S).filter
          (fun s => Arithmetic.residueChar (R.basePlace s.1).1 = p),
          (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
            Arithmetic.ordp s.1.1
              (R.qroot (show R.badFinset from s.1))) =
        ∑ p ∈ P,
          ∑ s : S,
            if Arithmetic.residueChar (R.basePlace s.1).1 = p then
              (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
                Arithmetic.ordp s.1.1
                  (R.qroot (show R.badFinset from s.1))
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
    _ = ∑ p ∈ P,
          ∑ b : T,
            if Arithmetic.residueChar b.1 = p then
              (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
                (2 * (D.prime.ℓ : ℝ))
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hFiber p
    _ = ∑ p ∈ P,
        ∑ b ∈ (Finset.univ : Finset T).filter
          (fun b => Arithmetic.residueChar b.1 = p),
          (iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_filter]

end JoshiTeich.Act1Scene1
