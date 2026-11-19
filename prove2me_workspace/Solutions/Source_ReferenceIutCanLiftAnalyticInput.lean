/-
Source: OrbicurveCores/U2/TheoremG.lean (`fixes_xP`) at revision
61616dcd77fbe45c083a8ebfa7cc80728f86e841, Apache-2.0.
The affine coordinate uses `Oka/Uniformization/FEtCurve.lean` (`FEt.xA`).
-/
import Solutions.Source_ReferenceIutCanLiftXDescent
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineCoordinateNormalizationSurjective

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.ReferenceIut.Anabelian.Genuine

variable {k : Type*} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The coordinate used in Theorem G is the image of the affine Weierstrass `x`. -/
theorem coordinateBaseNormalizationAlgEquiv_apply_x :
    coordinateBaseNormalizationAlgEquiv E (Affine.CoordinateRing.mk E.toAffine (C X)) =
      normalizationBaseX E :=
  coordinateToBaseNormalization_algebraMap_poly E X

local notation "A₀[" E "]" => AffineOrbicurvePresentation.A (normalizationPresentation E 1 ⊥ false)

/-- The analytic fixed-coordinate result on a finite extension yields the corresponding
statement for a cover of the actual unsigned normalization. -/
theorem canLift27ComplexAutomorphismsFixX_of_finite_algebra
    (hfix : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic]
      (B : Type) [CommRing B] [Algebra ℂ B] [Algebra A₀[E] B] [IsScalarTower ℂ A₀[E] B]
      [IsDedekindDomain B] [Module.Finite A₀[E] B] [FaithfulSMul A₀[E] B],
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
      (∀ w : Ideal B, w.IsMaximal → w.ramificationIdx A₀[E] = 1) →
      ∀ σ : B ≃ₐ[ℂ] B,
        σ (algebraMap A₀[E] B (normalizationBaseX E)) = algebraMap A₀[E] B (normalizationBaseX E)) :
    CanLift27ComplexAutomorphismsFixX := by
  intro E _ hj T π σ
  letI : Algebra A₀[E] T.A := π.f.toRingHom.toAlgebra
  have : IsScalarTower ℂ A₀[E] T.A := IsScalarTower.of_algebraMap_eq fun a => (π.f.commutes a).symm
  have : Module.Finite A₀[E] T.A := π.finite
  have : FaithfulSMul A₀[E] T.A := (faithfulSMul_iff_algebraMap_injective _ _).mpr π.injective
  have het (w : Ideal T.A) (hw : w.IsMaximal) : w.ramificationIdx A₀[E] = 1 := by
    have h := π.ramification w hw
    change w.ramificationIdx A₀[E] * T.mult w = 1 at h
    exact Nat.eq_one_of_mul_eq_one_left ((Nat.mul_comm _ _).trans h)
  exact hfix E T.A hj het σ

end AbcAdaptation.Reference.Iut.Anabelian
