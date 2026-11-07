import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPlaceSection
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

namespace JoshiTeich.Act1Scene1

open JoshiTeich.ReferenceIut
open NumberField
open scoped Classical

universe u
noncomputable section

variable {AG : AnabelianGeometry.{u}}
variable {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-SECTION-ALL-PLACES-INJECTIVE-20261108
source: IUT I Definition 3.1(e), `ValuationSection.sect`; Joshi III
`ss:val-sets-defn` (1030--1055), where the selected valuation set is the
image of the chosen section.
fidelity: packages the actual finite and infinite place choices carried by
`InitialThetaData.localData.sect` and proves that the full place section is
injective. The finite branch uses contraction uniqueness; the infinite branch
uses the equality of infinite-place comaps.
boundary: this is a concrete section certificate. It does not construct an
independent `L'` representative system, identify the image with paper `Voss`,
or prove any coverage, multiplicity, or mixed-moduli identity.
-/

noncomputable def iutInitialThetaPlaceSection :
    ModPlace D.F D.E → Place ↥D.prime.torsionField :=
  D.localData.sect.sect

theorem iutInitialThetaPlaceSection_injective :
    Function.Injective (iutInitialThetaPlaceSection D) := by
  intro v₁ v₂ h
  cases v₁ with
  | inl v₁ =>
      cases v₂ with
      | inl v₂ =>
          have hw : iutInitialThetaFinitePlaceSection D v₁ =
              iutInitialThetaFinitePlaceSection D v₂ :=
            Sum.inl.inj h
          exact congrArg Place.finite
            (iutInitialThetaFinitePlaceSection_injective D hw)
      | inr v₂ =>
          cases h
  | inr v₁ =>
      cases v₂ with
      | inl v₂ =>
          cases h
      | inr v₂ =>
          have hw : D.localData.sect.sectInf v₁ =
              D.localData.sect.sectInf v₂ :=
            Sum.inr.inj h
          haveI : (D.localData.sect.sectInf v₁).LiesOver v₁ :=
            D.localData.sect.sectInf_liesOver v₁
          haveI : (D.localData.sect.sectInf v₂).LiesOver v₂ :=
            D.localData.sect.sectInf_liesOver v₂
          have h₁ :=
            NumberField.InfinitePlace.LiesOver.comap_eq
              (D.localData.sect.sectInf v₁) v₁
          have h₂ :=
            NumberField.InfinitePlace.LiesOver.comap_eq
              (D.localData.sect.sectInf v₂) v₂
          have hc := congrArg
            (fun w : InfinitePlace ↥D.prime.torsionField =>
              w.comap (algebraMap (↥(fieldOfModuli D.F D.E))
                ↥D.prime.torsionField)) hw
          exact congrArg Sum.inr (h₁.symm.trans (hc.trans h₂))

noncomputable def iutInitialThetaPlaceSection_image_equiv :
    ModPlace D.F D.E ≃
      {w : Place ↥D.prime.torsionField //
        w ∈ D.localData.sect.V} := by
  let f : ModPlace D.F D.E →
      {w : Place ↥D.prime.torsionField //
        w ∈ D.localData.sect.V} :=
    fun v => ⟨iutInitialThetaPlaceSection D v, ⟨v, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro v₁ v₂ h
    exact iutInitialThetaPlaceSection_injective D (congrArg Subtype.val h)
  · rintro ⟨w, hw⟩
    change w ∈ Set.range (iutInitialThetaPlaceSection D) at hw
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩

end
end JoshiTeich.Act1Scene1
