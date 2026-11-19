/-
Source: Pi1/Orbicurve/Core.lean and Pi1/Orbicurve/Elliptic.lean at revision
ca7def953193f861a462aa0831eec8f0a31ff69f, Apache-2.0.
Original author: Christian Merten and the pi1 contributors.
See also Iut/Anabelian/Genuine/Realize.lean, Iut/Anabelian/Genuine/Punctured.lean,
and Iut/Anabelian/GenuineEtale.lean at revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedNormalizationGalois
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Model
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

universe u

variable {k : Type u} [Field k]

/-- Membership in the class of orbicurves that have a common finite étale cover with `X`. -/
def LocBar (X Y : AffineOrbicurvePresentation k) : Prop :=
  ∃ Z : AffineOrbicurvePresentation k, Nonempty (Cover Z X) ∧ Nonempty (Cover Z Y)

/-- `C` is a terminal object in the class of orbicurves with a common cover with `X`. -/
def IsCoreOf (X C : AffineOrbicurvePresentation k) : Prop :=
  LocBar X C ∧ ∀ Y : AffineOrbicurvePresentation k, LocBar X Y →
    Nonempty (Cover Y C) ∧ Subsingleton (Cover Y C)

end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical

universe u

noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

private def normalizationMultiplicity (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    (pm : Bool) → Ideal (coverCoordinateRing E ℓ M pm) → ℕ
  | false => fun _ => 1
  | true => FunctionFieldNormalization.ramificationMultiplicity
      (normalizationField_signed_le_unsigned E ℓ M)

/-- The affine presentation of the model orbicurve `(E, ℓ, M, ±)` on its normalization ring. -/
def normalizationPresentation (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    AffineOrbicurvePresentation k where
  A := coverCoordinateRing E ℓ M pm
  finiteType := finiteType_coverCoordinateRing E ℓ M pm
  not_isField := notField_coverCoordinateRing E ℓ M pm
  mult := normalizationMultiplicity E ℓ M pm
  mult_pos v hv := by
    cases pm
    · exact Nat.one_pos
    · exact FunctionFieldNormalization.ramificationMultiplicity_pos
        (transcendental_xG E) _ v hv
  finite_mult := by
    cases pm
    · simp [normalizationMultiplicity]
    · exact FunctionFieldNormalization.finite_ramificationMultiplicity
        (transcendental_xG E) _

attribute [local instance] signedNormalizationAlgebra

private theorem signedNormalizationRamificationCondition (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (w : Ideal (coverCoordinateRing E ℓ M false))
    (hw : w.IsMaximal) :
    (letI := (signedNormalizationRingMap E ℓ M).toRingHom.toAlgebra;
      w.ramificationIdx (coverCoordinateRing E ℓ M true)) * normalizationMultiplicity E ℓ M false w =
        normalizationMultiplicity E ℓ M true (w.comap (signedNormalizationRingMap E ℓ M)) := by
  letI : w.IsPrime := hw.isPrime
  let v : Ideal (coverCoordinateRing E ℓ M true) := w.comap (signedNormalizationRingMap E ℓ M)
  letI : v.IsPrime := Ideal.IsPrime.comap (signedNormalizationRingMap E ℓ M).toRingHom
  letI : w.LiesOver v := ⟨rfl⟩
  exact (mul_one _).trans (signedNormalizationMultiplicity_eq_ramificationIdx E ℓ M v w).symm

/-- The quotient by the sign action, with its actual closed-point multiplicities. -/
def signedNormalizationCover (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    AffineOrbicurvePresentation.Cover
      (normalizationPresentation E ℓ M false) (normalizationPresentation E ℓ M true) where
  f := signedNormalizationRingMap E ℓ M
  injective := signedNormalizationRingMap_injective E ℓ M
  isIntegral := signedNormalizationRingMap_isIntegral E ℓ M
  ramification := signedNormalizationRamificationCondition E ℓ M

end

end JoshiTeich.ReferenceIut.Anabelian.Genuine

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation (IsCoreOf)
open JoshiTeich.ReferenceIut.Anabelian (Orbicurve)
open JoshiTeich.ReferenceIut.Anabelian.Genuine (normalizationPresentation)

universe u

/-- The four rational exceptional `j`-invariants in [CanLift], Proposition 2.7. -/
def canLiftExceptionalJ : Finset ℚ := {0, 1728, 488095744 / 125, 1556068 / 81}

/-- [CanLift], Proposition 2.7 over characteristic-zero fields, on the normalized models. -/
def CanLift27 : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic],
    (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : k)) →
      IsCoreOf (normalizationPresentation E 1 ⊥ false) (normalizationPresentation E 1 ⊥ true)

/-- [CanLift], Proposition 2.7 over `ℂ`, on the same two normalized models. -/
def CanLift27Complex : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
    IsCoreOf (normalizationPresentation E 1 ⊥ false) (normalizationPresentation E 1 ⊥ true)

/-- The core relation on the affine presentations of the original model orbicurves. -/
def normalizationHasCore {k : Type u} [Field k] (X C : Orbicurve k) : Prop :=
  ∃ _ : CharZero k, IsCoreOf (normalizationPresentation X.E X.level X.M X.pm)
    (normalizationPresentation C.E C.level C.M C.pm)

/-- The characteristic-zero CanLift theorem supplies the once-punctured field for this relation. -/
theorem normalizationHasCore_oncePunctured (h27 : CanLift27.{u})
    {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]
    (hj : ∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : k)) :
    normalizationHasCore (Orbicurve.oncePunctured E)
      (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)) :=
  ⟨inferInstance, h27 k E hj⟩

end AbcAdaptation.Reference.Iut.Anabelian
