import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-SELECTED-BASE-SUPPORT-COVERAGE
source: the canonical odd multiplicative support and `placeUnder` from
`IutInitialThetaBadSupport.lean` and `IutPlacesOver.lean`, together with the
actual `InitialThetaData` finite-place section.
fidelity: isolates the exact coverage condition needed before the section-selected
base carrier can be identified with the full q-pilot support. The current
`InitialThetaData` interfaces prove only the inclusion; this theorem makes the
missing reverse inclusion explicit.
boundary: Scene1/Derived
-/

theorem iutInitialThetaOddSupportSelectedBasePlaces_eq_fullSupport_iff
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOddSupportSelectedBasePlaces D =
        IutOddMultiplicativeSupport D ↔
      ∀ w : NumberField.FinitePlace D.F,
        w ∈ IutOddMultiplicativeSupport D →
          iutInitialThetaSectionBasePlace D
              (iutPlaceUnder (F :=
                ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
                (Kt := D.F) w) = w := by
  constructor
  · intro hEq w hw
    have hwSelected : w ∈ iutInitialThetaOddSupportSelectedBasePlaces D := by
      rw [hEq]
      exact hw
    rcases hwSelected with ⟨v, hv, hsection⟩
    have hvUnder : v = iutPlaceUnder (F :=
        ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
        (Kt := D.F) w := by
      rw [← hsection]
      exact iutPlaceUnder_eq_of_liesOver
        (iutInitialThetaSectionBasePlace_liesOver D v)
    rw [← hvUnder]
    exact hsection
  · intro hCoverage
    apply Set.Subset.antisymm
    · exact iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D
    · intro w hw
      have hvMod : iutPlaceUnder (F :=
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
          (Kt := D.F) w ∈ iutVBadOddModSupportPort D := by
        rw [← iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
        exact mem_iutOddMultiplicativeModSupport_of_mem_support D hw
      exact ⟨iutPlaceUnder (F :=
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
          (Kt := D.F) w, hvMod, hCoverage w hw⟩

end

end JoshiTeich.Act1Scene1
