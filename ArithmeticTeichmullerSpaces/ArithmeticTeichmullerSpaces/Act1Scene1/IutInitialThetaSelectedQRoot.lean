import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPlaceSection
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVoss
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open WithZero

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-SELECTED-QROOT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean`,
`ValuationSection.sectFin` and `sectFin_liesOver`; `refer/iut/Iut/Tripod/CyclicTorsion.lean`,
`EllipticCurveData.VBadOdd`; `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`tateFamilyOfTorsion`.
fidelity: places selected by the actual InitialThetaData section over the complete
odd multiplicative moduli support are shown to belong to the corresponding full-support
torsion q-root carrier. At each selected place, the q-root power equals the actual
section Tate-family q parameter. This is an inclusion and local compatibility result;
it does not identify the selected image with the paper's `underline V^oss` or the
Scene1 link carrier.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

private theorem iutInitialThetaSelectedQRoot_algebraModK_eq_canonical
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    D.algebraModK =
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  calc
    ((D.algebraModK.algebraMap x : ↥D.prime.torsionField) : D.Fbar) =
        ((algebraMap D.F ↥D.prime.torsionField
          (algebraMap (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F x) :
            ↥D.prime.torsionField) : D.Fbar) := by
      exact congrArg Subtype.val
        (@IsScalarTower.algebraMap_apply
          (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
          ↥D.prime.torsionField _ _ _ _ _ D.algebraModK D.towerModK x)
    _ = (((JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem.algebraMap x :
        ↥D.prime.torsionField) : D.Fbar) := rfl

private theorem iutInitialThetaSelectedQRoot_section_liesOver_canonical
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    @JoshiTeich.ReferenceIut.FinitePlace.LiesOver
      _ _ _ _ _ _
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
      (iutInitialThetaFinitePlaceSection D v) v :=
  iutInitialThetaSelectedQRoot_algebraModK_eq_canonical D ▸
    iutInitialThetaFinitePlaceSection_liesOver D v

/-- Contract the place selected by `sectFin` from the torsion field to `D.F`. -/
noncomputable def iutInitialThetaSectionBasePlace
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    NumberField.FinitePlace D.F :=
  iutPlaceUnder (F := D.F) (Kt := ↥D.prime.torsionField)
    (iutInitialThetaFinitePlaceSection D v)

/-- The contracted section place lies over the moduli-field place it represents. -/
theorem iutInitialThetaSectionBasePlace_liesOver
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    Ideal.LiesOver (iutInitialThetaSectionBasePlace D v).maximalIdeal.asIdeal
      v.maximalIdeal.asIdeal := by
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  let K := ↥D.prime.torsionField
  let w := iutInitialThetaFinitePlaceSection D v
  let b := iutInitialThetaSectionBasePlace D v
  letI : Algebra M K :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hfieldHom :
      algebraMap M K =
        (algebraMap D.F K).comp (algebraMap M D.F) := by
    exact RingHom.ext fun x => rfl
  letI : IsScalarTower M D.F K := IsScalarTower.of_algebraMap_eq' hfieldHom
  letI : IsScalarTower (𝓞 M) (𝓞 D.F) (𝓞 K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hfieldHom x)
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal :=
    iutInitialThetaSelectedQRoot_section_liesOver_canonical D v
  haveI : w.maximalIdeal.asIdeal.LiesOver b.maximalIdeal.asIdeal :=
    iutPlaceUnder_liesOver (F := D.F) (Kt := K) w
  exact Ideal.LiesOver.tower_bot w.maximalIdeal.asIdeal b.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal

/-- Distinct moduli places have distinct section contractions to `D.F`. -/
theorem iutInitialThetaSectionBasePlace_injective
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Function.Injective (iutInitialThetaSectionBasePlace D) := by
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  letI : Algebra M D.F :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  intro v₁ v₂ h
  have h₁ : v₁ = iutPlaceUnder (F := M) (Kt := D.F)
      (iutInitialThetaSectionBasePlace D v₁) :=
    iutPlaceUnder_eq_of_liesOver
      (iutInitialThetaSectionBasePlace_liesOver D v₁)
  have h₂ : v₂ = iutPlaceUnder (F := M) (Kt := D.F)
      (iutInitialThetaSectionBasePlace D v₂) :=
    iutPlaceUnder_eq_of_liesOver
      (iutInitialThetaSectionBasePlace_liesOver D v₂)
  calc
    v₁ = iutPlaceUnder (F := M) (Kt := D.F)
        (iutInitialThetaSectionBasePlace D v₁) := h₁
    _ = iutPlaceUnder (F := M) (Kt := D.F)
        (iutInitialThetaSectionBasePlace D v₂) := by rw [h]
    _ = v₂ := h₂.symm

/-- The finite image of odd multiplicative moduli places under section contraction. -/
def iutInitialThetaOddSupportSelectedBasePlaces
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace D.F) :=
  iutInitialThetaSectionBasePlace D '' iutVBadOddModSupportPort D

theorem iutInitialThetaOddSupportSelectedBasePlaces_finite
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddSupportSelectedBasePlaces D).Finite := by
  exact (iutInitialThetaOddModSupport_finite D).image _

theorem iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOddSupportSelectedBasePlaces D ⊆
      (iutInitialThetaOddSupportBaseQPilotSource D).badPlaces := by
  rintro b ⟨v, hv, rfl⟩
  change iutInitialThetaSectionBasePlace D v ∈ IutOddMultiplicativeSupport D
  rw [← iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D] at hv
  rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport]
  exact ⟨v, hv, iutInitialThetaSectionBasePlace_liesOver D v⟩

/-- The actual section representative over an odd multiplicative moduli place,
viewed as a member of the full-support torsion q-root carrier. -/
noncomputable def iutInitialThetaOddSupportSelectedQRootPlace
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
  classical
  let K := ↥D.prime.torsionField
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let w := iutInitialThetaFinitePlaceSection D v
  let b := iutPlaceUnder (F := D.F) (Kt := K) w
  letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
      ↥D.prime.torsionField :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hfieldHom :
      algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
          ↥D.prime.torsionField =
        (algebraMap D.F ↥D.prime.torsionField).comp
          (algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F) := by
    exact RingHom.ext fun x => rfl
  letI : IsScalarTower M D.F K := IsScalarTower.of_algebraMap_eq' hfieldHom
  letI : IsScalarTower (𝓞 M) (𝓞 D.F) (𝓞 K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hfieldHom x)
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal :=
    iutInitialThetaSelectedQRoot_section_liesOver_canonical D v
  haveI : w.maximalIdeal.asIdeal.LiesOver b.maximalIdeal.asIdeal :=
    iutPlaceUnder_liesOver (F := D.F) (Kt := K) w
  have hbv : b.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal :=
    Ideal.LiesOver.tower_bot w.maximalIdeal.asIdeal b.maximalIdeal.asIdeal
      v.maximalIdeal.asIdeal
  have hvMod : v ∈ IutOddMultiplicativeModSupport D := by
    rw [iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
    exact hv
  have hOdd : Odd (Arithmetic.residueChar b) := by
    rw [Arithmetic.residueChar_eq_of_liesOver hbv]
    exact hvMod.1
  have hMult : JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E b :=
    hvMod.2.2 b hbv
  have hSupport : b ∈ IutOddMultiplicativeSupport D := ⟨hOdd, hMult⟩
  have hwCarrier : w ∈ iutBadPlacesOver (k := D.F) (K := K) B.badPlaces := by
    change w ∈ iutBadPlacesOver (k := D.F) (K := K)
      (IutOddMultiplicativeSupport D)
    exact ⟨b, hSupport, iutPlaceUnder_liesOver (F := D.F) (Kt := K) w⟩
  have hwFinset :=
    (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite w).mpr hwCarrier
  exact ⟨w, hwFinset⟩

/-- The underlying torsion-field places selected as q-root representatives by
the actual section over the complete odd multiplicative support. -/
def iutInitialThetaOddSupportSelectedQRootPlaces
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  {w | ∃ (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
      (hv : v ∈ iutVBadOddModSupportPort D),
      (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1 = w}

theorem iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1 =
      iutInitialThetaFinitePlaceSection D v := by
  rfl

/-- The selected q-root places are exactly the odd Tate section places from
the Voss characterization of the actual IUT section. -/
theorem iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOddSupportSelectedQRootPlaces D =
      iutInitialThetaOddTateSectionPlaces D := by
  rw [iutInitialThetaOddTateSectionPlaces_eq_selectedSupport]
  ext w
  simp only [iutInitialThetaOddSupportSelectedQRootPlaces, Set.mem_ofPred_eq,
    iutInitialThetaOddMultiplicativeSelectedPlaces, Set.mem_image]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv,
      (iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section D v hv).trans h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv,
      (iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section D v hv).symm.trans h⟩

theorem iutInitialThetaOddSupportSelectedQRootPlaces_finite
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddSupportSelectedQRootPlaces D).Finite := by
  rw [iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces,
    iutInitialThetaOddTateSectionPlaces_eq_selectedSupport]
  exact (iutInitialThetaOddModSupport_finite D).image _

/-- At the section-selected representative, the q-root power is the q parameter
of the Tate structure selected by the actual InitialThetaData. -/
theorem iutInitialThetaOddSupportSelectedQRootPlace_qroot_pow_eq_sectionTate
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
    (iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ (2 * D.prime.ℓ) =
      ((iutInitialThetaTateFamilyOfTorsion D).S s.1
        ⟨v, hv, iutInitialThetaSelectedQRoot_section_liesOver_canonical D v⟩).t.q := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
  letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
      ↥D.prime.torsionField :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hsBad : JoshiTeich.ReferenceIut.IsBadPlace D.E D.prime.torsionField
      (iutVBadOddModSupportPort D) s.1 := by
    exact ⟨v, hv, iutInitialThetaSelectedQRoot_section_liesOver_canonical D v⟩
  calc
    R.qroot s ^ (2 * D.prime.ℓ) =
        R.completionMap s
          (B.tateParameter (R.basePlace s)) := R.qroot_pow_eq s
    _ = iutEmbedCompletion
        (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) s)
        (B.tateParameter (IutTorsionQRootSource.basePlaceOf (B := B) s)) := rfl
    _ = ((iutInitialThetaTateFamilyOfTorsion D).S s.1 hsBad).t.q := by
      exact (iutInitialThetaOddSupportTateFamily_q_eq_baseParameter D s).symm

/-- At the actual section representative, rescaling the arithmetic `ordp` of
the selected q-root by the absolute ramification index gives the local
q-order used by the paper's `|uniformizer| = p⁻¹` normalization. -/
theorem iutInitialThetaOddSupportSelectedQRootPlace_ramIdx_mul_ordp_eq_sectionQOrder
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
    let S := (iutInitialThetaTateFamilyOfTorsion D).S s.1
      ⟨v, hv, iutInitialThetaSelectedQRoot_section_liesOver_canonical D v⟩
    (Arithmetic.ramIdx s.1 : ℝ) *
        Arithmetic.ordp s.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) =
      (iutCompletionQOrder s.1 S.t.q : ℝ) /
        (2 * (D.prime.ℓ : ℝ)) := by
  classical
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
      ↥D.prime.torsionField :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hsBad : JoshiTeich.ReferenceIut.IsBadPlace D.E D.prime.torsionField
      (iutVBadOddModSupportPort D) s.1 :=
    ⟨v, hv, iutInitialThetaSelectedQRoot_section_liesOver_canonical D v⟩
  let S := (iutInitialThetaTateFamilyOfTorsion D).S s.1 hsBad
  have hpow : R.qroot s ^ (2 * D.prime.ℓ) = S.t.q := by
    simpa [s, S, hsBad] using
      iutInitialThetaOddSupportSelectedQRootPlace_qroot_pow_eq_sectionTate D v hv
  have hqVal := iutCompletionQOrder_valued s.1 S.t.q
    S.t.q.ne_zero S.t.norm_lt_one
  have hqOrd0 := Arithmetic.ordp_eq_of_valued s.1 S.t.q
    (-(iutCompletionQOrder s.1 S.t.q : ℤ)) hqVal
  have hqOrd : Arithmetic.ordp s.1 S.t.q =
      (iutCompletionQOrder s.1 S.t.q : ℝ) /
        (Arithmetic.ramIdx s.1 : ℝ) := by
    rw [hqOrd0]
    push_cast
    ring
  have hpowOrd := congrArg (Arithmetic.ordp s.1) hpow
  rw [Arithmetic.ordp_pow, hqOrd] at hpowOrd
  push_cast at hpowOrd
  have he : (Arithmetic.ramIdx s.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos s.1).ne'
  have hell : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have htwoell : (2 * (D.prime.ℓ : ℝ)) ≠ 0 := by positivity
  calc
    (Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s) =
        ((Arithmetic.ramIdx s.1 : ℝ) *
          ((2 * (D.prime.ℓ : ℝ)) * Arithmetic.ordp s.1 (R.qroot s))) /
          (2 * (D.prime.ℓ : ℝ)) := by
      field_simp [hell]
    _ = ((Arithmetic.ramIdx s.1 : ℝ) *
          ((iutCompletionQOrder s.1 S.t.q : ℝ) /
            (Arithmetic.ramIdx s.1 : ℝ))) /
          (2 * (D.prime.ℓ : ℝ)) := by rw [hpowOrd]
    _ = (iutCompletionQOrder s.1 S.t.q : ℝ) /
          (2 * (D.prime.ℓ : ℝ)) := by
      field_simp [he, htwoell]

/-- The section-selected q-root has the canonical base-field q-order after
accounting for the absolute ramification index of its contracted place. -/
theorem iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    Arithmetic.ordp s.1 (R.qroot s) =
      (B.qOrder (R.basePlace s) : ℝ) /
        (2 * (D.prime.ℓ : ℝ) *
          Arithmetic.ramIdx (R.basePlace s).1) := by
  classical
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have hTateValued : ∀ w : B.badFinset,
      Valued.v (B.tateParameter w) = exp (-(B.qOrder w : ℤ)) := by
    intro w
    exact iutCompletionQOrder_valued w.1 (B.tateParameter w)
      (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w)
  have hEll : 0 < D.prime.ℓ := by
    have h := D.prime.five_le
    omega
  have hOrder := IutTorsionQRootSource.canonical_qroot_ordp_eq
    B R.qroot R.qroot_pow_eq hTateValued hEll s
  have hbase : R.basePlace s =
      IutTorsionQRootSource.basePlaceOf (B := B) s := by
    apply Subtype.ext
    calc
      (R.basePlace s).1 = iutPlaceUnder s.1 :=
        iutPlaceUnder_eq_of_liesOver (R.liesOver s)
      _ = (IutTorsionQRootSource.basePlaceOf (B := B) s).1 :=
        (iutPlaceUnder_eq_of_liesOver
          (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) s)).symm
  simpa [s, R, B, hbase] using hOrder

/-- The q-root source base place is the contraction of the actual section place. -/
theorem iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    (R.basePlace s).1 = iutInitialThetaSectionBasePlace D v := by
  classical
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  have hcontract : (R.basePlace s).1 = iutPlaceUnder s.1 :=
    iutPlaceUnder_eq_of_liesOver (R.liesOver s)
  have hs : s.1 = iutInitialThetaFinitePlaceSection D v := by
    simpa [s] using iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section D v hv
  simpa [hs, iutInitialThetaSectionBasePlace] using hcontract

/-! The selected q-root carrier is a finite subcarrier of the full-support
source. Keeping it as a subtype makes the representative-to-base-place map
available for later finite-sum accounting without changing the source carrier
used by the local q-root construction. -/
def iutInitialThetaOddSupportSelectedQRootSourcePlaces
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  {s | s.1 ∈ iutInitialThetaOddSupportSelectedQRootPlaces D}

theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces D).Finite := by
  exact Set.toFinite _

theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_image_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset =>
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1) ''
        iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
      iutInitialThetaOddSupportSelectedBasePlaces D := by
  ext b
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases hs with ⟨v, hv, hsection⟩
    refine ⟨v, hv, ?_⟩
    have hcontract :
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 =
          iutPlaceUnder s.1 :=
      iutPlaceUnder_eq_of_liesOver
        ((iutInitialThetaOddSupportTorsionQRootSource D).liesOver s)
    calc
      iutInitialThetaSectionBasePlace D v = iutPlaceUnder
          (iutInitialThetaFinitePlaceSection D v) := rfl
      _ = iutPlaceUnder
          (iutInitialThetaOddSupportSelectedQRootPlace D v hv).1 := by rfl
      _ = iutPlaceUnder s.1 := congrArg iutPlaceUnder hsection
      _ = ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 :=
        hcontract.symm
  · rintro ⟨v, hv, rfl⟩
    let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv
    refine ⟨s, ?_, ?_⟩
    · exact ⟨v, hv, rfl⟩
    · change ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 =
        iutInitialThetaSectionBasePlace D v
      simpa [s] using
        iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v hv

/-! The section contraction has no multiplicity on the selected carrier: the
representative-to-base-place map is injective after restricting to the
section-selected q-root subtype. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_injective
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Function.Injective (fun s :
        {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
          s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} =>
      (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1) := by
  intro s t hst
  rcases s.2 with ⟨v, hv, hsection⟩
  rcases t.2 with ⟨v', hv', hsection'⟩
  have hsectionSubtype :
      iutInitialThetaOddSupportSelectedQRootPlace D v hv = s.1 :=
    Subtype.ext hsection
  have hsectionSubtype' :
      iutInitialThetaOddSupportSelectedQRootPlace D v' hv' = t.1 :=
    Subtype.ext hsection'
  have hbase : iutInitialThetaSectionBasePlace D v =
      iutInitialThetaSectionBasePlace D v' := by
    calc
      iutInitialThetaSectionBasePlace D v =
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
            (iutInitialThetaOddSupportSelectedQRootPlace D v hv)).1 :=
        (iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace
          D v hv).symm
      _ = ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1).1 :=
        congrArg (fun x =>
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace x).1)
          hsectionSubtype
      _ = ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace t.1).1 :=
        congrArg Subtype.val hst
      _ = ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
            (iutInitialThetaOddSupportSelectedQRootPlace D v' hv')).1 :=
        congrArg (fun x =>
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace x).1)
          hsectionSubtype'.symm
      _ = iutInitialThetaSectionBasePlace D v' :=
        iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace
          D v' hv'
  have hvv' : v = v' := iutInitialThetaSectionBasePlace_injective D hbase
  subst v'
  apply Subtype.ext
  have hselected :
      iutInitialThetaOddSupportSelectedQRootPlace D v hv =
        iutInitialThetaOddSupportSelectedQRootPlace D v hv' := by
    apply Subtype.ext
    exact
      (iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section D v hv).trans
        (iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section D v hv').symm
  exact hsectionSubtype.symm.trans (hselected.trans hsectionSubtype')

/-- The selected q-root source subtype and its selected contracted base-place
subtype have the canonical contraction equivalence. -/
noncomputable def iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} ≃
      {b : NumberField.FinitePlace D.F //
        b ∈ iutInitialThetaOddSupportSelectedBasePlaces D} := by
  let f :
      {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} →
      {b : NumberField.FinitePlace D.F //
        b ∈ iutInitialThetaOddSupportSelectedBasePlaces D} := fun s =>
    ⟨((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1).1, by
      rw [← iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_image_eq D]
      exact ⟨s.1, s.2, rfl⟩⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro s t hst
    have hstBase :
        (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1 =
          (iutInitialThetaOddSupportTorsionQRootSource D).basePlace t.1 := by
      have hstVal :
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1).1 =
            ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace t.1).1 :=
        congrArg (fun x => x.1) hst
      exact Subtype.ext hstVal
    exact iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_injective D hstBase
  · intro b
    have hbImage : b.1 ∈
        (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset =>
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1) ''
          iutInitialThetaOddSupportSelectedQRootSourcePlaces D := by
      rw [iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_image_eq D]
      exact b.2
    rcases hbImage with ⟨s, hs, hsb⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    exact hsb

end

end JoshiTeich.Act1Scene1
