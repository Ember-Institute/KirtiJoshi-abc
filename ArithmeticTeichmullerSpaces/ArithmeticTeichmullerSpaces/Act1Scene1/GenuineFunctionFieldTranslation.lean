import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassTranscendentalPointEvaluation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineGenericPointTranslation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual Weierstrass generic point and Mathlib point base change.
fidelity: original proof. Constructs translation on the original function
field by evaluating at the translated generic point in that same field.
The opposite constant point gives the inverse. The ambient algebraic closure
is used only to transfer the already proved transcendence result.
boundary: Scene1/Derived. Does not construct an ambient closure automorphism,
an infinity cusp, or a geometry producer.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u v
open WeierstrassCurve Polynomial
open JoshiTeich.Act1Scene1.WeierstrassTranscendentalPointEvaluation
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

local instance : DecidableEq E.toAffine.FunctionField :=
  fun a b => Classical.propDecidable (a = b)

local instance : (E⁄E.toAffine.FunctionField).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k E.toAffine.FunctionField)).IsElliptic

/-- The original generic point, before embedding its coordinates into `Ω E`. -/
def functionFieldGenericPoint : (E⁄E.toAffine.FunctionField).toAffine.Point :=
  Affine.Point.some (xF E) (yF E) (by
    rw [← Affine.equation_iff_nonsingular]
    exact equation_xF_yF E)

/-- Constant points in the original function field. -/
def functionFieldBase : E.toAffine.Point →+
    (E⁄E.toAffine.FunctionField).toAffine.Point :=
  Affine.Point.baseChange (W' := E.toAffine) k E.toAffine.FunctionField

private theorem map_functionFieldGenericPoint :
    Affine.Point.map (W' := E.toAffine) (ιF E) (functionFieldGenericPoint E) =
      genericPoint E := rfl

private theorem map_functionFieldBase (T : E.toAffine.Point) :
    Affine.Point.map (W' := E.toAffine) (ιF E) (functionFieldBase E T) = base E T := by
  exact Affine.Point.map_baseChange (W' := E.toAffine) (ιF E) T

private theorem ptX_map {K : Type v} [Field K] [Algebra k K]
    (f : E.toAffine.FunctionField →ₐ[k] K)
    (P : (E⁄E.toAffine.FunctionField).toAffine.Point) :
    ptX (Affine.Point.map (W' := E.toAffine) f P) = f (ptX P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

private theorem ptY_map {K : Type v} [Field K] [Algebra k K]
    (f : E.toAffine.FunctionField →ₐ[k] K)
    (P : (E⁄E.toAffine.FunctionField).toAffine.Point) :
    ptY (Affine.Point.map (W' := E.toAffine) f P) = f (ptY P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

theorem functionFieldGenericPoint_add_base_ne_zero (T : E.toAffine.Point) :
    functionFieldGenericPoint E + functionFieldBase E T ≠ 0 := by
  intro h
  apply genericPoint_add_base_ne_zero E T
  have hm := congrArg (Affine.Point.map (W' := E.toAffine) (ιF E)) h
  simpa only [map_add, map_zero, map_functionFieldGenericPoint,
    map_functionFieldBase] using hm

theorem functionFieldGenericPoint_add_base_x_transcendental (T : E.toAffine.Point) :
    Transcendental k (ptX (functionFieldGenericPoint E + functionFieldBase E T)) := by
  intro hx
  apply genericPoint_add_base_x_transcendental E T
  have hm : ιF E (ptX (functionFieldGenericPoint E + functionFieldBase E T)) =
      ptX (genericPoint E + base E T) := by
    rw [← ptX_map, map_add, map_functionFieldGenericPoint, map_functionFieldBase]
  rw [← hm]
  rcases hx with ⟨p, hp, hroot⟩
  refine ⟨p, hp, ?_⟩
  rw [Polynomial.aeval_algHom_apply, hroot, map_zero]

/-- Pullback by translation by the actual constant point `T`. -/
def functionFieldTranslationAlgHom (T : E.toAffine.Point) :
    E.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField :=
  functionFieldAlgHom E (functionFieldGenericPoint E + functionFieldBase E T)
    (functionFieldGenericPoint_add_base_ne_zero E T)
    (functionFieldGenericPoint_add_base_x_transcendental E T)

@[simp] theorem functionFieldTranslationAlgHom_xF (T : E.toAffine.Point) :
    functionFieldTranslationAlgHom E T (xF E) =
      ptX (functionFieldGenericPoint E + functionFieldBase E T) :=
  functionFieldAlgHom_X E _ _ _

@[simp] theorem functionFieldTranslationAlgHom_yF (T : E.toAffine.Point) :
    functionFieldTranslationAlgHom E T (yF E) =
      ptY (functionFieldGenericPoint E + functionFieldBase E T) :=
  functionFieldAlgHom_Y E _ _ _

/-- The induced map on points sends the original generic point to its translation. -/
theorem functionFieldTranslationAlgHom_genericPoint (T : E.toAffine.Point) :
    Affine.Point.map (W' := E.toAffine) (functionFieldTranslationAlgHom E T)
        (functionFieldGenericPoint E) =
      functionFieldGenericPoint E + functionFieldBase E T := by
  have hP := functionFieldGenericPoint_add_base_ne_zero E T
  generalize hq : functionFieldGenericPoint E + functionFieldBase E T = P at hP ⊢
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y h =>
    change Affine.Point.some _ _ _ = Affine.Point.some x y h
    congr 1
    · exact (functionFieldTranslationAlgHom_xF E T).trans (congrArg ptX hq)
    · exact (functionFieldTranslationAlgHom_yF E T).trans (congrArg ptY hq)

private theorem functionFieldPointMap_base
    (f : E.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
    (T : E.toAffine.Point) :
    Affine.Point.map (W' := E.toAffine) f (functionFieldBase E T) =
      functionFieldBase E T := by
  exact Affine.Point.map_baseChange (W' := E.toAffine) f T

/-- Opposite actual translations compose to the identity on the original function field. -/
theorem functionFieldTranslationAlgHom_neg_comp (T : E.toAffine.Point) :
    (functionFieldTranslationAlgHom E (-T)).comp
        (functionFieldTranslationAlgHom E T) =
      AlgHom.id k E.toAffine.FunctionField := by
  have hpoint :
      Affine.Point.map (W' := E.toAffine) (functionFieldTranslationAlgHom E (-T))
        (Affine.Point.map (W' := E.toAffine) (functionFieldTranslationAlgHom E T)
          (functionFieldGenericPoint E)) = functionFieldGenericPoint E := by
    rw [functionFieldTranslationAlgHom_genericPoint, map_add,
      functionFieldTranslationAlgHom_genericPoint, functionFieldPointMap_base,
      map_neg]
    simp only [add_assoc, neg_add_cancel, add_zero]
  apply functionFieldAlgHom_ext E
  · have hx := congrArg ptX hpoint
    rw [ptX_map, ptX_map] at hx
    exact hx
  · have hy := congrArg ptY hpoint
    rw [ptY_map, ptY_map] at hy
    exact hy

/-- Translation by `T` is an automorphism of the original Weierstrass function field. -/
def functionFieldTranslationEquiv (T : E.toAffine.Point) :
    E.toAffine.FunctionField ≃ₐ[k] E.toAffine.FunctionField :=
  AlgEquiv.ofAlgHom (functionFieldTranslationAlgHom E T)
    (functionFieldTranslationAlgHom E (-T))
    (by simpa only [neg_neg] using functionFieldTranslationAlgHom_neg_comp E (-T))
    (functionFieldTranslationAlgHom_neg_comp E T)

@[simp] theorem functionFieldTranslationEquiv_xF (T : E.toAffine.Point) :
    functionFieldTranslationEquiv E T (xF E) =
      ptX (functionFieldGenericPoint E + functionFieldBase E T) :=
  functionFieldTranslationAlgHom_xF E T

@[simp] theorem functionFieldTranslationEquiv_yF (T : E.toAffine.Point) :
    functionFieldTranslationEquiv E T (yF E) =
      ptY (functionFieldGenericPoint E + functionFieldBase E T) :=
  functionFieldTranslationAlgHom_yF E T

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
