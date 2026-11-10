import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineShiftedDivisionPointTranscendence
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassPointRawChartFractionField

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); the same selected division-point field,
its actual translation automorphism, and the original Weierstrass evaluation.
fidelity: evaluates the original function field at the translated same selected
point. Coordinate ext identifies this evaluation with the original division
field evaluation precomposed by its actual function-field translation. Thus
the image is the same actual full division-coordinate field.
Original composition of existing project theorems; no reference code copied.
boundary: no normalization residue or prime chart identity.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open JoshiTeich.Act1Scene1.WeierstrassTranscendentalPointEvaluation
open scoped Classical
noncomputable section
universe u

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

local instance shiftedDivisionFunctionFieldImage_decidableEq :
    DecidableEq (Ω E) := fun a b => Classical.propDecidable (a = b)

/-- The original function field evaluated at the same selected division point translated by T. -/
def shiftedDivisionPointFunctionFieldAlgHom
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    E.toAffine.FunctionField →ₐ[k] Ω E := by
  let P : (E⁄(Ω E)).toAffine.Point :=
    Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T)
  have hx : Transcendental k (ptX P) := by
    exact Qpt_add_base_x_transcendental E n hn T
  have hP : P ≠ 0 := by
    intro h
    exact hx.ne_zero (by rw [h]; rfl)
  exact functionFieldAlgHom E P hP hx

/-- The named shifted map is evaluation at that exact point, for any proofs of its properties. -/
theorem shiftedDivisionPointFunctionFieldAlgHom_eq_functionFieldAlgHom
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point)
    (hP : Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T) ≠ 0)
    (hx : Transcendental k (ptX (Affine.Point.add (W := (E⁄(Ω E)).toAffine)
      (Qpt E n) (base E T)))) :
    shiftedDivisionPointFunctionFieldAlgHom E n hn T =
      functionFieldAlgHom E
        (Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T)) hP hx := by
  rfl

/-- The shifted evaluation is the original selected-point evaluation after field translation. -/
theorem shiftedDivisionPointFunctionFieldAlgHom_eq
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    shiftedDivisionPointFunctionFieldAlgHom E n hn T =
      (divisionPointFunctionFieldAlgHom E n hn).comp
        (functionFieldTranslationEquiv E T).toAlgHom := by
  let P : (E⁄(Ω E)).toAffine.Point :=
    Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T)
  have hx : Transcendental k (ptX P) := Qpt_add_base_x_transcendental E n hn T
  have hP : P ≠ 0 := by
    intro h
    exact hx.ne_zero (by rw [h]; rfl)
  let qx : QField E n :=
    ⟨ptX (Qpt E n), IntermediateField.subset_adjoin _ _ (by simp)⟩
  let qy : QField E n :=
    ⟨ptY (Qpt E n), IntermediateField.subset_adjoin _ _ (by simp)⟩
  have hqx : divisionPointFunctionFieldEquiv E n hn (xF E) = qx := by
    apply Subtype.ext
    change divisionPointFunctionFieldAlgHom E n hn (xF E) = ptX (Qpt E n)
    exact divisionPointFunctionFieldAlgHom_X E n hn
  have hqy : divisionPointFunctionFieldEquiv E n hn (yF E) = qy := by
    apply Subtype.ext
    change divisionPointFunctionFieldAlgHom E n hn (yF E) = ptY (Qpt E n)
    exact divisionPointFunctionFieldAlgHom_Y E n hn
  have hxcomp :
      divisionPointFunctionFieldAlgHom E n hn (functionFieldTranslationEquiv E T (xF E)) =
        (divisionFieldTranslationEquiv E n hn T qx : QField E n) := by
    rw [← coe_divisionPointFunctionFieldEquiv E n hn
      (functionFieldTranslationEquiv E T (xF E)),
      ← divisionFieldTranslationEquiv_apply_equiv, hqx]
  have hycomp :
      divisionPointFunctionFieldAlgHom E n hn (functionFieldTranslationEquiv E T (yF E)) =
        (divisionFieldTranslationEquiv E n hn T qy : QField E n) := by
    rw [← coe_divisionPointFunctionFieldEquiv E n hn
      (functionFieldTranslationEquiv E T (yF E)),
      ← divisionFieldTranslationEquiv_apply_equiv, hqy]
  apply functionFieldAlgHom_ext E
  · calc
      shiftedDivisionPointFunctionFieldAlgHom E n hn T (xF E) =
          ptX (Affine.Point.add (W := (E⁄(Ω E)).toAffine)
            (Qpt E n) (base E T)) := by
              exact functionFieldAlgHom_X E P hP hx
      _ = (divisionFieldTranslationEquiv E n hn T qx : QField E n) :=
        (divisionFieldTranslationEquiv_X E n hn T).symm.trans rfl
      _ = divisionPointFunctionFieldAlgHom E n hn
          (functionFieldTranslationEquiv E T (xF E)) := hxcomp.symm
  · calc
      shiftedDivisionPointFunctionFieldAlgHom E n hn T (yF E) =
          ptY (Affine.Point.add (W := (E⁄(Ω E)).toAffine)
            (Qpt E n) (base E T)) := by
              exact functionFieldAlgHom_Y E P hP hx
      _ = (divisionFieldTranslationEquiv E n hn T qy : QField E n) :=
        (divisionFieldTranslationEquiv_Y E n hn T).symm.trans rfl
      _ = divisionPointFunctionFieldAlgHom E n hn
          (functionFieldTranslationEquiv E T (yF E)) := hycomp.symm

/-- Translation does not change the field range of the actual division evaluation. -/
theorem shiftedDivisionPointFunctionFieldAlgHom_fieldRange
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    (shiftedDivisionPointFunctionFieldAlgHom E n hn T).fieldRange =
      (QField E n).restrictScalars k := by
  rw [shiftedDivisionPointFunctionFieldAlgHom_eq E n hn T]
  have hrange :
      ((divisionPointFunctionFieldAlgHom E n hn).comp
        (functionFieldTranslationEquiv E T).toAlgHom).fieldRange =
      (divisionPointFunctionFieldAlgHom E n hn).fieldRange := by
    apply SetLike.ext
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨functionFieldTranslationEquiv E T a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(functionFieldTranslationEquiv E T).symm a, by simp⟩
  rw [hrange, divisionPointFunctionFieldAlgHom_fieldRange E n hn]

/-- The translated same point's two coordinates generate the original full division field. -/
theorem Qpt_add_base_coordinateField
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    IntermediateField.adjoin k
      ({ptX (Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T)),
        ptY (Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T))} : Set (Ω E)) =
      (QField E n).restrictScalars k := by
  let P : (E⁄(Ω E)).toAffine.Point :=
    Affine.Point.add (W := (E⁄(Ω E)).toAffine) (Qpt E n) (base E T)
  have hx : Transcendental k (ptX P) := Qpt_add_base_x_transcendental E n hn T
  have hP : P ≠ 0 := by
    intro h
    exact hx.ne_zero (by rw [h]; rfl)
  exact (JoshiTeich.Act1Scene1.WeierstrassPointRawChartFractionField.fieldRange_eq_adjoin E P hP hx).symm.trans
    ((congrArg AlgHom.fieldRange
      (shiftedDivisionPointFunctionFieldAlgHom_eq_functionFieldAlgHom E n hn T hP hx)).symm.trans
      (shiftedDivisionPointFunctionFieldAlgHom_fieldRange E n hn T))

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
