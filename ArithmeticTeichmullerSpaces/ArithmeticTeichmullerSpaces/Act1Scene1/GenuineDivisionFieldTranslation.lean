import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldNegation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineFunctionFieldTranslation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual division-coordinate field and original function-field translation.
fidelity: original proof. Transports the established function-field
translation along its established evaluation equivalence with `QField E n`.
Proves that the transported automorphism translates the same selected
division point by the same constant point, in the original ambient closure.
boundary: Scene1/Derived. Fixed-base and ambient lifting are separate consumers.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

local instance : DecidableEq E.toAffine.FunctionField :=
  fun a b => Classical.propDecidable (a = b)

local instance : (E⁄E.toAffine.FunctionField).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k E.toAffine.FunctionField)).IsElliptic

/-- Translation transported to the original selected division-coordinate field. -/
def divisionFieldTranslationEquiv (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    QField E n ≃ₐ[k] QField E n :=
  (divisionPointFunctionFieldEquiv E n hn).symm.trans
    ((functionFieldTranslationEquiv E T).trans (divisionPointFunctionFieldEquiv E n hn))

@[simp] theorem divisionFieldTranslationEquiv_apply_equiv
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) (a : E.toAffine.FunctionField) :
    divisionFieldTranslationEquiv E n hn T (divisionPointFunctionFieldEquiv E n hn a) =
      divisionPointFunctionFieldEquiv E n hn (functionFieldTranslationEquiv E T a) := by
  simp only [divisionFieldTranslationEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

private theorem evaluation_genericPoint (n : ℕ) (hn : 0 < n) :
    Affine.Point.map (W' := E.toAffine) (divisionPointFunctionFieldAlgHom E n hn)
        (functionFieldGenericPoint E) = Qpt E n := by
  have hQne : Qpt E n ≠ 0 := by
    rw [Qpt_eq_divSys E hn]
    exact divSys_ne_zero E n hn
  rcases hQ : Qpt E n with _ | ⟨x, y, hns⟩
  · exact False.elim (hQne hQ)
  · change Affine.Point.some _ _ _ = Affine.Point.some x y hns
    congr 1
    · simpa only [hQ, ptX, xF] using divisionPointFunctionFieldAlgHom_X E n hn
    · simpa only [hQ, ptY, yF] using divisionPointFunctionFieldAlgHom_Y E n hn

private theorem evaluation_base (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    Affine.Point.map (W' := E.toAffine) (divisionPointFunctionFieldAlgHom E n hn)
      (functionFieldBase E T) = base E T := by
  exact Affine.Point.map_baseChange (W' := E.toAffine)
    (divisionPointFunctionFieldAlgHom E n hn) T

/-- The selected division point over its original coordinate field. -/
def divisionFieldPoint (n : ℕ) (hn : 0 < n) : (E⁄(QField E n)).toAffine.Point :=
  Affine.Point.map (W' := E.toAffine) (divisionPointFunctionFieldEquiv E n hn).toAlgHom
    (functionFieldGenericPoint E)

/-- The original inclusion of the selected division field into the same closure. -/
def divisionFieldInclusion (n : ℕ) : QField E n →ₐ[k] Ω E :=
  ((QField E n).restrictScalars k).val

/-- The descended point retains the original selected division point. -/
theorem divisionFieldPoint_map (n : ℕ) (hn : 0 < n) :
    Affine.Point.map (W' := E.toAffine) (divisionFieldInclusion E n)
        (divisionFieldPoint E n hn) = Qpt E n := by
  rw [divisionFieldPoint, Affine.Point.map_map]
  change Affine.Point.map (W' := E.toAffine) (divisionPointFunctionFieldAlgHom E n hn)
    (functionFieldGenericPoint E) = Qpt E n
  exact evaluation_genericPoint E n hn

/-- The transported automorphism translates the actual selected division point. -/
theorem divisionFieldTranslationEquiv_pointMap
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    Affine.Point.map (W' := E.toAffine)
        ((divisionFieldInclusion E n).comp (divisionFieldTranslationEquiv E n hn T).toAlgHom)
        (divisionFieldPoint E n hn) = Qpt E n + base E T := by
  have hhom :
      ((divisionFieldInclusion E n).comp (divisionFieldTranslationEquiv E n hn T).toAlgHom).comp
          (divisionPointFunctionFieldEquiv E n hn).toAlgHom =
        (divisionPointFunctionFieldAlgHom E n hn).comp
          (functionFieldTranslationEquiv E T).toAlgHom := by
    apply AlgHom.ext
    intro a
    change ((divisionFieldTranslationEquiv E n hn T
      (divisionPointFunctionFieldEquiv E n hn a) : QField E n) : Ω E) = _
    rw [divisionFieldTranslationEquiv_apply_equiv, coe_divisionPointFunctionFieldEquiv]
    rfl
  rw [divisionFieldPoint, Affine.Point.map_map, hhom, ← Affine.Point.map_map]
  have htr : Affine.Point.map (W' := E.toAffine) (functionFieldTranslationEquiv E T).toAlgHom
      (functionFieldGenericPoint E) = functionFieldGenericPoint E + functionFieldBase E T :=
    functionFieldTranslationAlgHom_genericPoint E T
  rw [htr, map_add, evaluation_genericPoint, evaluation_base]

private theorem ptX_map {n : ℕ} (f : QField E n →ₐ[k] Ω E)
    (P : (E⁄(QField E n)).toAffine.Point) :
    ptX (Affine.Point.map (W' := E.toAffine) f P) = f (ptX P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

private theorem ptY_map {n : ℕ} (f : QField E n →ₐ[k] Ω E)
    (P : (E⁄(QField E n)).toAffine.Point) :
    ptY (Affine.Point.map (W' := E.toAffine) f P) = f (ptY P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

private theorem divisionPoint_X_mem_QField (n : ℕ) : ptX (Qpt E n) ∈ QField E n :=
  IntermediateField.subset_adjoin _ _ (by simp)

private theorem divisionPoint_Y_mem_QField (n : ℕ) : ptY (Qpt E n) ∈ QField E n :=
  IntermediateField.subset_adjoin _ _ (by simp)

@[simp] theorem divisionFieldTranslationEquiv_X
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    ((divisionFieldTranslationEquiv E n hn T
      ⟨ptX (Qpt E n), divisionPoint_X_mem_QField E n⟩ : QField E n) : Ω E) =
        ptX (Qpt E n + base E T) := by
  have hx : ptX (divisionFieldPoint E n hn) =
      (⟨ptX (Qpt E n), divisionPoint_X_mem_QField E n⟩ : QField E n) := by
    apply Subtype.ext
    change divisionFieldInclusion E n (ptX (divisionFieldPoint E n hn)) = ptX (Qpt E n)
    rw [← ptX_map, divisionFieldPoint_map]
  have h := congrArg ptX (divisionFieldTranslationEquiv_pointMap E n hn T)
  rw [ptX_map, hx] at h
  exact h

@[simp] theorem divisionFieldTranslationEquiv_Y
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    ((divisionFieldTranslationEquiv E n hn T
      ⟨ptY (Qpt E n), divisionPoint_Y_mem_QField E n⟩ : QField E n) : Ω E) =
        ptY (Qpt E n + base E T) := by
  have hy : ptY (divisionFieldPoint E n hn) =
      (⟨ptY (Qpt E n), divisionPoint_Y_mem_QField E n⟩ : QField E n) := by
    apply Subtype.ext
    change divisionFieldInclusion E n (ptY (divisionFieldPoint E n hn)) = ptY (Qpt E n)
    rw [← ptY_map, divisionFieldPoint_map]
  have h := congrArg ptY (divisionFieldTranslationEquiv_pointMap E n hn T)
  rw [ptY_map, hy] at h
  exact h

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
