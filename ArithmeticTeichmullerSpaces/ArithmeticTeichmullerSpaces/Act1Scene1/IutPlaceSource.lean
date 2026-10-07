import ArithmeticTeichmullerSpaces.Act1Scene1.FieldOrientationAudit
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped NumberField

universe uF

/-!
source-id: IUT-COR312-BAD-PLACES-OVER
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`,
`badPlacesOver`; `refer/iut/Iut/Cor312/ThetaData/PlacesOver.lean`,
the finite-fibre argument; and `refer/iut/Iut/Concrete/LocalTheory.lean`,
`QPilotData.badFinset_spec`.
fidelity: the place carrier and its finite enumeration are derived from the
base-field bad locus and the ideal-theoretic `LiesOver` relation.  Tate roots,
elliptic-curve reduction, and the torsion-field source remain separate fields.
boundary: Scene1/Derived

The reference project does not choose an unrelated finite set for the q-pilot:
it defines `V(F)^bad` as the places over `V_mod^bad` and proves finiteness from
finite fibres of finite places.  This file ports that carrier layer for the
mathlib `NumberField.FinitePlace` representation.
-/

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

/-!
The IUT q-pilot lives on the field `F`, while its bad locus is defined by a
finite set of places of the field of moduli below `F`.  This constructor keeps
that two-field orientation explicit and derives the carrier fields from
`iutBadPlacesOver`; callers provide the local Tate parameter and admissibility
condition on the canonical finite subtype. The local integer order is derived
from the completion valuation.
-/
noncomputable def IutBaseQPilotSource.ofOverVBad
    {k F : Type uF} [Field k] [NumberField k] [Field F] [NumberField F]
    [Algebra k F]
    (ell : ℕ)
    (VBad : Set (NumberField.FinitePlace k)) (hVBad : VBad.Finite)
    (weight : NumberField.FinitePlace F → ℝ)
    (weight_eq_qPilotWeight : ∀ w, weight w = Arithmetic.qPilotWeight w)
    (tateParameter : ∀ w : iutBadPlacesOverFinset (k := k) (K := F) VBad hVBad,
      w.1.maximalIdeal.adicCompletion F)
    (tateParameter_ne_zero : ∀ w, tateParameter w ≠ 0)
    (tateParameter_norm_lt_one : ∀ w, ‖tateParameter w‖ < 1)
    (qOrder_coprime : ∀ w,
      Nat.Coprime ell (iutCompletionQOrder w.1 (tateParameter w))) :
    IutBaseQPilotSource F ell :=
  { badPlaces := iutBadPlacesOver (k := k) (K := F) VBad
    badFinset := iutBadPlacesOverFinset (k := k) (K := F) VBad hVBad
    badFinset_spec := by
      ext w
      exact mem_iutBadPlacesOverFinset_iff VBad hVBad w
    weight := weight
    weight_eq_qPilotWeight := weight_eq_qPilotWeight
    tateParameter := tateParameter
    tateParameter_ne_zero := tateParameter_ne_zero
    tateParameter_norm_lt_one := tateParameter_norm_lt_one
    qOrder_coprime := qOrder_coprime }

namespace IutBaseQPilotSource

variable {F : Type uF} [Field F] [NumberField F]
variable {ell : ℕ} (B : IutBaseQPilotSource F ell)

lemma badPlaces_finite : B.badPlaces.Finite := by
  rw [← B.badFinset_spec]
  exact B.badFinset.finite_toSet

end IutBaseQPilotSource

/-!
The reference `placeUnder` is the contraction of a torsion-place prime to the
base ring of integers.  Porting this definition makes the base-place witness
canonical instead of choosing an unrelated member of the over-locus.
-/

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
        exact Ideal.under_ne_bot_of_integral_mem hx0 hx
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

/-!
The torsion carrier is the over-locus of the base q-pilot carrier.  The
constructor below makes that carrier canonical and derives a base-place
witness from its `LiesOver` evidence; the completion map and q-root equation
remain source obligations.
-/

namespace IutTorsionQRootSource

variable {F Kt : Type uF} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
variable [Algebra F Kt] {ell : ℕ} {B : IutBaseQPilotSource F ell}

lemma exists_basePlace
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    ∃ w : B.badFinset,
      Ideal.LiesOver v.1.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal := by
  have hv : v.1 ∈ iutBadPlacesOver (k := F) (K := Kt) B.badPlaces :=
    (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite v.1).mp v.2
  rcases hv with ⟨w, hw, hvw⟩
  have hUnder : iutPlaceUnder v.1 ∈ B.badPlaces := by
    rw [← iutPlaceUnder_eq_of_liesOver hvw]
    exact hw
  have hUnder' : iutPlaceUnder v.1 ∈ B.badFinset := by
    exact (Set.ext_iff.mp B.badFinset_spec _).mpr hUnder
  exact ⟨⟨iutPlaceUnder v.1, hUnder'⟩,
    iutPlaceUnder_liesOver (F := F) (Kt := Kt) v.1⟩

noncomputable def basePlaceOf
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) : B.badFinset :=
  Classical.choose (exists_basePlace (B := B) v)

lemma basePlaceOf_liesOver
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    Ideal.LiesOver v.1.maximalIdeal.asIdeal
      (basePlaceOf (B := B) v).1.maximalIdeal.asIdeal :=
  Classical.choose_spec (exists_basePlace (B := B) v)

lemma basePlaceOf_eq_placeUnder
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    (basePlaceOf (B := B) v).1 = iutPlaceUnder v.1 := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  change (basePlaceOf (B := B) v).1.maximalIdeal =
    (iutPlaceUnder v.1).maximalIdeal
  apply IsDedekindDomain.HeightOneSpectrum.ext
  have h := basePlaceOf_liesOver (B := B) v
  haveI : v.1.maximalIdeal.asIdeal.LiesOver
      (basePlaceOf (B := B) v).1.maximalIdeal.asIdeal := h
  rw [iutPlaceUnder_maximalIdeal (F := F) (Kt := Kt) v.1]
  simpa only [Ideal.under_def] using
    (Ideal.over_def v.1.maximalIdeal.asIdeal
      (basePlaceOf (B := B) v).1.maximalIdeal.asIdeal)

noncomputable def ofOverBaseBad
    (B : IutBaseQPilotSource F ell)
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_ne_zero : ∀ v, qroot v ≠ 0)
    (completionMap : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      (basePlaceOf (B := B) v).1.maximalIdeal.adicCompletion F →+*
        v.1.maximalIdeal.adicCompletion Kt)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        completionMap v (B.tateParameter (basePlaceOf (B := B) v))) :
    IutTorsionQRootSource F Kt ell B :=
  { badFinset := iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite
    basePlace := fun v => basePlaceOf (B := B) v
    liesOver := fun v => basePlaceOf_liesOver (B := B) v
    qroot := qroot
    qroot_ne_zero := qroot_ne_zero
    completionMap := completionMap
    qroot_pow_eq := qroot_pow_eq }

lemma ofOverBaseBad_badFinset
    (B : IutBaseQPilotSource F ell)
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_ne_zero : ∀ v, qroot v ≠ 0)
    (completionMap : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      (basePlaceOf (B := B) v).1.maximalIdeal.adicCompletion F →+*
        v.1.maximalIdeal.adicCompletion Kt)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        completionMap v (B.tateParameter (basePlaceOf (B := B) v))) :
    (ofOverBaseBad B qroot qroot_ne_zero completionMap qroot_pow_eq).badFinset =
      iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces B.badPlaces_finite :=
  rfl

end IutTorsionQRootSource

end JoshiTeich.Act1Scene1
