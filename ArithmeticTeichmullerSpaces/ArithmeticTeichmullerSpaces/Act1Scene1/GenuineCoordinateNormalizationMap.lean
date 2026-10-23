import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedBaseNormalizationRing
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationFinite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's Weierstrass coordinate-ring basis, integral closure and fraction fields.
fidelity: constructs the natural map from the original Weierstrass coordinate
ring to the actual unsigned base normalization. It is injective and finite,
preserves the original function-field embedding and polynomial coordinate,
and induces the proved equivalence of fraction fields.
boundary: Scene1/Derived. Surjectivity, the original-coordinate scheme
identification, orbicurve comparison and the full producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- Every original coordinate-ring element is integral over the polynomial x-coordinate. -/
theorem coordinateRing_isIntegral : Algebra.IsIntegral k[X] E.toAffine.CoordinateRing := by
  have : Module.Finite k[X] E.toAffine.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis E.toAffine)
  infer_instance

def coordinatePolynomialNormalizationMap :
    E.toAffine.CoordinateRing →ₐ[k[X]] integralClosure k[X] E.toAffine.FunctionField :=
  (IsScalarTower.toAlgHom k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField).codRestrict
    (integralClosure k[X] E.toAffine.FunctionField) fun a =>
      (coordinateRing_isIntegral E).isIntegral a |>.algebraMap

/-- The natural normalization map preserves the original ambient function-field values. -/
def coordinateToBaseNormalization :
    E.toAffine.CoordinateRing →ₐ[k] coverCoordinateRing E 1 ⊥ false :=
  (polynomialNormalizationRingAlgEquiv E).toAlgHom.comp
    ((coordinatePolynomialNormalizationMap E).restrictScalars k)

@[simp] theorem coe_coordinateToBaseNormalization (a : E.toAffine.CoordinateRing) :
    (((coordinateToBaseNormalization E a : coverCoordinateRing E 1 ⊥ false) :
      normalizationField E 1 ⊥ false) : Ω E) =
        ιF E (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField a) := rfl

theorem coordinateToBaseNormalization_injective : Function.Injective (coordinateToBaseNormalization E) := by
  intro a b hab
  have h := congrArg (fun c : coverCoordinateRing E 1 ⊥ false =>
    ((c : normalizationField E 1 ⊥ false) : Ω E)) hab
  exact IsFractionRing.injective E.toAffine.CoordinateRing E.toAffine.FunctionField
    ((ιF E).injective h)

theorem coordinateToBaseNormalization_algebraMap_poly (p : k[X]) :
    coordinateToBaseNormalization E (algebraMap k[X] E.toAffine.CoordinateRing p) =
      signedNormalizationRingMap E 1 ⊥ (signedBasePolynomialAlgEquiv E p) := by
  rw [coordinateToBaseNormalization, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
    AlgHom.commutes]
  exact baseNormalizationRingEquiv_square E p

theorem coordinateToBaseNormalization_finite : (coordinateToBaseNormalization E).toRingHom.Finite := by
  have hnorm : (signedNormalizationRingMap E 1 ⊥).toRingHom.Finite :=
    FunctionFieldNormalization.ringMap_finite (transcendental_xG E) _
  have hpoly : (signedBasePolynomialAlgEquiv E).toRingHom.Finite :=
    RingHom.Finite.of_surjective _ (signedBasePolynomialAlgEquiv E).surjective
  have hcomp : (coordinateToBaseNormalization E).toRingHom.comp
      (algebraMap k[X] E.toAffine.CoordinateRing) =
        (signedNormalizationRingMap E 1 ⊥).toRingHom.comp
          (signedBasePolynomialAlgEquiv E).toRingHom :=
    RingHom.ext (coordinateToBaseNormalization_algebraMap_poly E)
  apply RingHom.Finite.of_comp_finite (f := algebraMap k[X] E.toAffine.CoordinateRing)
  rw [hcomp]
  exact hnorm.comp hpoly

/-- Use the original coordinate-ring embedding for the actual normalization field. -/
@[instance_reducible] def coordinateNormalizationFieldAlgebra :
    Algebra E.toAffine.CoordinateRing (normalizationField E 1 ⊥ false) :=
  ((normalizationBaseFunctionFieldEquiv E).toRingHom.comp
    (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField)).toAlgebra

attribute [local instance] coordinateNormalizationFieldAlgebra

def coordinateNormalizationFractionFieldEquiv :
    E.toAffine.FunctionField ≃ₐ[E.toAffine.CoordinateRing] normalizationField E 1 ⊥ false :=
  AlgEquiv.ofRingEquiv (f := normalizationBaseFunctionFieldEquiv E) fun _ => rfl

theorem coordinateNormalizationField_isFractionRing :
    IsFractionRing E.toAffine.CoordinateRing (normalizationField E 1 ⊥ false) :=
  IsFractionRing.of_algEquiv (coordinateNormalizationFractionFieldEquiv E)

/-- Every normalization-field element is a fraction of original coordinate-ring elements. -/
theorem coordinateNormalizationField_fraction (z : normalizationField E 1 ⊥ false) :
    ∃ a b : E.toAffine.CoordinateRing, b ≠ 0 ∧
      (coordinateToBaseNormalization E a : normalizationField E 1 ⊥ false) /
        (coordinateToBaseNormalization E b : normalizationField E 1 ⊥ false) = z := by
  have := coordinateNormalizationField_isFractionRing E
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective E.toAffine.CoordinateRing z
  exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
