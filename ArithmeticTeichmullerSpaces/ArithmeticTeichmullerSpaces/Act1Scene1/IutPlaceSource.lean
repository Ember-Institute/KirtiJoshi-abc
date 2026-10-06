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
`iutBadPlacesOver`; callers only provide the local Tate/q-order data on the
canonical finite subtype.
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
    (qOrder : ∀ w : iutBadPlacesOverFinset (k := k) (K := F) VBad hVBad, ℕ)
    (qOrder_pos : ∀ w, 0 < qOrder w)
    (qOrder_coprime : ∀ w, Nat.Coprime ell (qOrder w)) :
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
    qOrder := qOrder
    qOrder_pos := qOrder_pos
    qOrder_coprime := qOrder_coprime }

lemma IutBaseQPilotSource.ofOverVBad_badPlaces
    {k F : Type uF} [Field k] [NumberField k] [Field F] [NumberField F]
    [Algebra k F]
    (ell : ℕ)
    (VBad : Set (NumberField.FinitePlace k)) (hVBad : VBad.Finite)
    (weight : NumberField.FinitePlace F → ℝ)
    (weight_eq_qPilotWeight : ∀ w, weight w = Arithmetic.qPilotWeight w)
    (tateParameter : ∀ w : iutBadPlacesOverFinset (k := k) (K := F) VBad hVBad,
      w.1.maximalIdeal.adicCompletion F)
    (tateParameter_ne_zero : ∀ w, tateParameter w ≠ 0)
    (qOrder : ∀ w : iutBadPlacesOverFinset (k := k) (K := F) VBad hVBad, ℕ)
    (qOrder_pos : ∀ w, 0 < qOrder w)
    (qOrder_coprime : ∀ w, Nat.Coprime ell (qOrder w)) :
    (IutBaseQPilotSource.ofOverVBad ell VBad hVBad weight weight_eq_qPilotWeight
      tateParameter tateParameter_ne_zero qOrder qOrder_pos qOrder_coprime).badPlaces =
      iutBadPlacesOver (k := k) (K := F) VBad := by
  rfl

namespace IutBaseQPilotSource

variable {F : Type uF} [Field F] [NumberField F]
variable {ell : ℕ} (B : IutBaseQPilotSource F ell)

lemma badPlaces_finite : B.badPlaces.Finite := by
  rw [← B.badFinset_spec]
  exact B.badFinset.finite_toSet

end IutBaseQPilotSource

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
  have hw' : w ∈ B.badFinset := by
    exact (Set.ext_iff.mp B.badFinset_spec w).mpr hw
  exact ⟨⟨w, hw'⟩, by simpa using hvw⟩

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
