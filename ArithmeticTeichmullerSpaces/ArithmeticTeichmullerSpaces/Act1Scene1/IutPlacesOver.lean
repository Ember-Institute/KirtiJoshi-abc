import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace JoshiTeich.Act1Scene1

open scoped NumberField

universe uF

/-!
source-id: IUT-COR312-PLACES-OVER-AND-PLACE-UNDER
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`,
`badPlacesOver`; `refer/iut/Iut/Cor312/ThetaData/PlacesOver.lean`,
the finite-fibre argument; and `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean`,
`placeUnder` and `liesOver_placeUnder`.
fidelity: ports the finite over-place carrier and the canonical contraction
from the torsion field to the base field for mathlib finite places.
boundary: Scene1/Derived
-/

/-- Finite places of `K` lying over a place in the base carrier. -/
def iutBadPlacesOver
    {k K : Type uF} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (VBad : Set (NumberField.FinitePlace k)) :
    Set (NumberField.FinitePlace K) :=
  {w | ∃ v ∈ VBad,
    Ideal.LiesOver w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal}

lemma finite_places_liesOver
    {k K : Type uF} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (v : NumberField.FinitePlace k) :
    {w : NumberField.FinitePlace K |
      Ideal.LiesOver w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal}.Finite := by
  classical
  refine Set.Finite.of_finite_image
    (f := fun w : NumberField.FinitePlace K => w.maximalIdeal.asIdeal) ?_ ?_
  · refine
      (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K)).finite_toSet.subset ?_
    rintro _ ⟨w, hw, rfl⟩
    haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hw
    exact
      (IsDedekindDomain.mem_primesOverFinset_iff v.maximalIdeal.ne_bot (𝓞 K)).mpr
        ⟨inferInstance, inferInstance⟩
  · intro w₁ _ w₂ _ h
    exact NumberField.FinitePlace.maximalIdeal_injective
      (IsDedekindDomain.HeightOneSpectrum.ext h)

lemma iutBadPlacesOver_finite
    {k K : Type uF} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (VBad : Set (NumberField.FinitePlace k)) (hVBad : VBad.Finite) :
    (iutBadPlacesOver VBad : Set (NumberField.FinitePlace K)).Finite := by
  classical
  change
    {w : NumberField.FinitePlace K |
      ∃ v ∈ VBad,
        Ideal.LiesOver w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal}.Finite
  have hUnion :
      (⋃ v ∈ VBad, {w : NumberField.FinitePlace K |
        Ideal.LiesOver w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal}).Finite :=
    hVBad.biUnion (fun v _ => finite_places_liesOver (K := K) v)
  refine hUnion.subset ?_
  rintro w ⟨v, hv, hw⟩
  exact Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨hv, hw⟩⟩

noncomputable def iutBadPlacesOverFinset
    {k K : Type uF} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (VBad : Set (NumberField.FinitePlace k)) (hVBad : VBad.Finite) :
    Finset (NumberField.FinitePlace K) :=
  (iutBadPlacesOver_finite VBad hVBad).toFinset

lemma mem_iutBadPlacesOverFinset_iff
    {k K : Type uF} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (VBad : Set (NumberField.FinitePlace k)) (hVBad : VBad.Finite)
    (w : NumberField.FinitePlace K) :
    w ∈ iutBadPlacesOverFinset VBad hVBad ↔ w ∈ iutBadPlacesOver VBad := by
  rw [iutBadPlacesOverFinset, Set.Finite.mem_toFinset]

/-! The canonical base place is the contraction of the torsion-place prime. -/
noncomputable def iutPlaceUnder
    {F Kt : Type uF} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] (v : NumberField.FinitePlace Kt) :
    NumberField.FinitePlace F :=
  NumberField.FinitePlace.mk
    { asIdeal := v.maximalIdeal.asIdeal.comap (algebraMap (𝓞 F) (𝓞 Kt))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
          v.maximalIdeal.ne_bot
        exact Ideal.comap_ne_bot_of_integral_mem hx0 hx
          (Algebra.IsIntegral.isIntegral x) }

lemma iutPlaceUnder_maximalIdeal
    {F Kt : Type uF} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] (v : NumberField.FinitePlace Kt) :
    (iutPlaceUnder v).maximalIdeal.asIdeal =
      v.maximalIdeal.asIdeal.comap (algebraMap (𝓞 F) (𝓞 Kt)) := by
  rw [iutPlaceUnder, NumberField.FinitePlace.maximalIdeal_mk]

lemma iutPlaceUnder_liesOver
    {F Kt : Type uF} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] (v : NumberField.FinitePlace Kt) :
    Ideal.LiesOver v.maximalIdeal.asIdeal
      (iutPlaceUnder (F := F) (Kt := Kt) v).maximalIdeal.asIdeal := by
  exact ⟨by
    rw [iutPlaceUnder_maximalIdeal (F := F) (Kt := Kt) v]⟩

lemma iutPlaceUnder_eq_of_liesOver
    {F Kt : Type uF} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt}
    {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    w = iutPlaceUnder v := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  change w.maximalIdeal = (iutPlaceUnder v).maximalIdeal
  apply IsDedekindDomain.HeightOneSpectrum.ext
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  rw [iutPlaceUnder_maximalIdeal (F := F) (Kt := Kt) v]
  simpa only [Ideal.under_def] using
    (Ideal.over_def v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)

end JoshiTeich.Act1Scene1
