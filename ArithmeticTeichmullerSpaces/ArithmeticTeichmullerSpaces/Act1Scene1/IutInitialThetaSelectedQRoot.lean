import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPlaceSection

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

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

end

end JoshiTeich.Act1Scene1
