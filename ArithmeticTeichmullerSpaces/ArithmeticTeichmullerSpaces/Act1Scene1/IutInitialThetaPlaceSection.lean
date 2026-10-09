import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadOddPort
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped NumberField

universe u

/-!
source-id: IUT-COR312-INITIAL-THETA-PLACE-SECTION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean`,
`ValuationSection.sectFin` and `sectFin_liesOver`; `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`InitialThetaData.localData`; `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean`,
`placeUnder` and `liesOver_placeUnder`.
fidelity: projects the actual finite-place section selected by `InitialThetaData` to
the moduli field and its fixed-field torsion extension, proves it is injective, and
maps the odd multiplicative support into the corresponding over-place carrier. This
does not identify the selected `VBad` with the full support or construct theta data.
boundary: Scene1/Derived
-/

/-- The finite-place representative map carried by the actual initial Theta data. -/
noncomputable def iutInitialThetaFinitePlaceSection
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) →
      NumberField.FinitePlace ↥D.prime.torsionField :=
  D.localData.sect.sectFin

/-- Each selected torsion-field place lies over its moduli-field place. -/
theorem iutInitialThetaFinitePlaceSection_liesOver
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    JoshiTeich.ReferenceIut.FinitePlace.LiesOver (iutInitialThetaFinitePlaceSection D v) v :=
  D.localData.sect.sectFin_liesOver v

/-- The chosen representative map is injective because a place has a unique contraction. -/
theorem iutInitialThetaFinitePlaceSection_injective
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Function.Injective (iutInitialThetaFinitePlaceSection D) := by
  intro v₁ v₂ h
  have h₁ : v₁ = iutPlaceUnder
      (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
      (Kt := ↥D.prime.torsionField)
      (iutInitialThetaFinitePlaceSection D v₁) :=
    iutPlaceUnder_eq_of_liesOver
      (iutInitialThetaFinitePlaceSection_liesOver D v₁)
  have h₂ : v₂ = iutPlaceUnder
      (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
      (Kt := ↥D.prime.torsionField)
      (iutInitialThetaFinitePlaceSection D v₂) :=
    iutPlaceUnder_eq_of_liesOver
      (iutInitialThetaFinitePlaceSection_liesOver D v₂)
  calc
    v₁ = iutPlaceUnder
        (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
        (Kt := ↥D.prime.torsionField)
        (iutInitialThetaFinitePlaceSection D v₁) := h₁
    _ = iutPlaceUnder
        (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
        (Kt := ↥D.prime.torsionField)
        (iutInitialThetaFinitePlaceSection D v₂) := congrArg _ h
    _ = v₂ := h₂.symm

/-- The image of the odd multiplicative support under the actual selected section. -/
noncomputable def iutInitialThetaOddMultiplicativeSelectedPlaces
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  iutInitialThetaFinitePlaceSection D '' iutVBadOddModSupportPort D

/-- Selected representatives of the odd multiplicative support lie over that support. -/
theorem iutInitialThetaOddMultiplicativeSelectedPlaces_subset_overSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOddMultiplicativeSelectedPlaces D ⊆
      iutBadPlacesOver (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
        (K := ↥D.prime.torsionField) (iutVBadOddModSupportPort D) := by
  rintro w ⟨v, hv, rfl⟩
  exact ⟨v, hv, iutInitialThetaFinitePlaceSection_liesOver D v⟩

end JoshiTeich.Act1Scene1
