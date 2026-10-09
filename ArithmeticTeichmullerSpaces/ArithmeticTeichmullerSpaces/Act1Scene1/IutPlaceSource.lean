import ArithmeticTeichmullerSpaces.Act1Scene1.IutQSourceContract
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped NumberField

universe uF

/-!
The IUT q-pilot lives on the field `F`, while its bad locus is defined by a
finite set of places of the field of moduli below `F`.  This constructor keeps
that two-field orientation explicit and derives the carrier fields from
`iutBadPlacesOver`; callers provide the local Tate parameter on the canonical
finite subtype. The IUT normalized order and its admissibility condition are
attached with the chosen uniformizer in `IutCompletionTateValuation`, where the
order is proved equal to the completion-valuation order.
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
    (tateParameter_norm_lt_one : ∀ w, ‖tateParameter w‖ < 1) :
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
    tateParameter_norm_lt_one := tateParameter_norm_lt_one }

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
