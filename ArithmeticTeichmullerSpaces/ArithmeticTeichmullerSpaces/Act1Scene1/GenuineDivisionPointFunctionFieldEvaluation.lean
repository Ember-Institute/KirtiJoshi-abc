import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointEvaluation

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-POINT-FUNCTION-FIELD-EVALUATION
source: IUT I Definition 3.1(d); the actual chosen division point and
Weierstrass function field.
fidelity: extends the already injective coordinate-ring evaluation at the
same actual `Qpt` through the pinned fraction-ring universal property.
boundary: Scene1/Derived. The image is not yet identified with `QField E n`,
and this leaf does not prove the Cartesian tensor square.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

/-- Fraction-field evaluation at the same actual division point. -/
def divisionPointFunctionFieldAlgHom (n : ℕ) (hn : 0 < n) :
    E.toAffine.FunctionField →ₐ[k] Ω E :=
  IsFractionRing.liftAlgHom (divisionPointCoordinateMap_injective E n hn)

@[simp] theorem divisionPointFunctionFieldAlgHom_algebraMap
    (n : ℕ) (hn : 0 < n) (a : E.toAffine.CoordinateRing) :
    divisionPointFunctionFieldAlgHom E n hn
        (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField a) =
      divisionPointCoordinateAlgHom E n a := by
  exact IsFractionRing.lift_algebraMap (divisionPointCoordinateMap_injective E n hn) a

theorem divisionPointFunctionFieldAlgHom_injective
    (n : ℕ) (hn : 0 < n) :
    Function.Injective (divisionPointFunctionFieldAlgHom E n hn) := by
  exact RingHom.injective _

@[simp] theorem divisionPointFunctionFieldAlgHom_X
    (n : ℕ) (hn : 0 < n) :
    divisionPointFunctionFieldAlgHom E n hn
        (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
          (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X))) =
      ptX (Qpt E n) := by
  rw [divisionPointFunctionFieldAlgHom_algebraMap,
    divisionPointCoordinateAlgHom_X]

@[simp] theorem divisionPointFunctionFieldAlgHom_Y
    (n : ℕ) (hn : 0 < n) :
    divisionPointFunctionFieldAlgHom E n hn
        (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
          (Affine.CoordinateRing.mk E.toAffine Polynomial.X)) =
      ptY (Qpt E n) := by
  rw [divisionPointFunctionFieldAlgHom_algebraMap,
    divisionPointCoordinateAlgHom_Y]

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
