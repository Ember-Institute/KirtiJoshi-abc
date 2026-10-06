/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateTorsionResidue

/-!
source-id: IUT-COR312-TORSION-CARDINALITY-TRANSFER
source: `iut`: `refer/iut/Iut/Anabelian/Torsion.lean` and
`refer/iut/Iut/Anabelian/LocalInputs.lean`.
fidelity: ports the rank-two torsion cardinality and injective localization argument
to abstract additive groups. The global basis and local maps remain explicit inputs.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

universe uG uA uK

noncomputable section

/-- A global `ell`-torsion subgroup with a chosen rank-two `ZMod ell` basis. -/
structure IutGlobalTorsionBasis (G : Type uG) [AddCommGroup G] (ell : ℕ) where
  torsion : AddSubgroup G
  torsion_le : torsion ≤ AddSubgroup.torsionBy G ell
  basis : ↥torsion ≃+ (Fin 2 → ZMod ell)

namespace IutGlobalTorsionBasis

variable {G : Type uG} [AddCommGroup G] {ell : ℕ}
variable (T : IutGlobalTorsionBasis G ell)

lemma card_eq_pow_two : Nat.card T.torsion = ell ^ 2 := by
  rw [Nat.card_congr T.basis.toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

lemma card_eq_mul : Nat.card T.torsion = ell * ell := by
  rw [T.card_eq_pow_two, pow_two]

end IutGlobalTorsionBasis

/-- An injective localization map from global points to a local additive group. -/
structure IutTorsionLocalMap {G : Type uG} [AddCommGroup G] {ell : ℕ}
    (T : IutGlobalTorsionBasis G ell) (A : Type uA) [AddCommGroup A] where
  toLocal : G →+ A
  injective : Function.Injective toLocal

namespace IutTorsionLocalMap

variable {G : Type uG} [AddCommGroup G] {A : Type uA} [AddCommGroup A]
variable {ell : ℕ} (T : IutGlobalTorsionBasis G ell)
variable (L : IutTorsionLocalMap T A)

def image : AddSubgroup A := T.torsion.map L.toLocal

lemma image_le_localTorsion : L.image ≤ iutTorsion A ell := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ AddSubgroup.torsionBy G ell := T.torsion_le hx
  rw [AddSubgroup.torsionBy.nsmul_iff] at hx' ⊢
  rw [← map_nsmul, hx', map_zero]

lemma card_localTorsion_lower_bound
    (T : IutGlobalTorsionBasis G ell) (L : IutTorsionLocalMap T A)
    {K : Type uK} [NormedField K]
    (S : IutTateQuotientUniformization K A) (hEll : 0 < ell) :
    ell * ell ≤ Nat.card ↥(iutTorsion A ell) := by
  letI : NeZero ell := ⟨Nat.ne_of_gt hEll⟩
  haveI : Finite ↥(iutTorsion A ell) := S.finite_torsion
  calc
    ell * ell = Nat.card T.torsion := T.card_eq_mul.symm
    _ = Nat.card ↥(L.image) :=
      Nat.card_congr
        (AddSubgroup.equivMapOfInjective T.torsion L.toLocal L.injective).toEquiv
    _ ≤ Nat.card ↥(iutTorsion A ell) :=
      AddSubgroup.card_le_of_le (L.image_le_localTorsion T)

end IutTorsionLocalMap

namespace IutTorsionQRootSource

universe uF uKt uE

variable {F Kt : Type uF} [Field F] [NumberField F]
variable [Field Kt] [NumberField Kt] [Algebra F Kt]
variable {ell : ℕ} {B : IutBaseQPilotSource F ell}

/-- Build the q-root source from a global full-torsion basis and injective local maps.

This derives the local `ell²` bound before applying the Tate-residue root-class argument. -/
noncomputable def ofOverBaseBadWithCanonicalCompletionMap_ofGlobalTorsionBasisAndSquareRoot
    (B : IutBaseQPilotSource F ell)
    (E : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite → Type uE)
    [∀ w, AddCommGroup (E w)]
    (S : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite,
        IutTateQuotientUniformization (w.1.maximalIdeal.adicCompletion Kt) (E w))
    (G : Type uG) [AddCommGroup G]
    (T : IutGlobalTorsionBasis G ell)
    (L : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, IutTorsionLocalMap T (E w))
    (hEll : 0 < ell)
    (hq : ∀ w,
      ((S w).q : w.1.maximalIdeal.adicCompletion Kt) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w)))
    (squareRoot : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, w.1.maximalIdeal.adicCompletion Kt)
    (hodd : Odd ell)
    (squareRoot_pow_eq : ∀ w,
      squareRoot w ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) :
    IutTorsionQRootSource F Kt ell B :=
  ofOverBaseBadWithCanonicalCompletionMap_ofTateUniformizationAndSquareRoot
    B E S hEll
    (fun w => IutTorsionLocalMap.card_localTorsion_lower_bound T (L w) (S w) hEll)
    hq squareRoot hodd squareRoot_pow_eq

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
