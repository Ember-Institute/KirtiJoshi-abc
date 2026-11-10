import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassTranscendentalPointEvaluation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: JT-SCENE1-GENUINE-DIVISION-POINT-EVALUATION
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the original coordinate evaluation and the same point under field inclusion.
fidelity: both coordinate formulas and the lifted function-field map commute
with the supplied inclusion. The same point, x, y and coefficient field are
preserved. No image-field or normalization identity is assumed.
Original composition of existing project theorems; no reference code copied.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassPointEvaluationNaturality

open WeierstrassCurve
open JoshiTeich.ReferenceIut.Anabelian
open WeierstrassTranscendentalPointEvaluation
noncomputable section

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] (E : WeierstrassCurve k) [E.IsElliptic]
  (f : K →ₐ[k] L)

local instance pointEvaluationNaturality_decidableEq_K : DecidableEq K :=
  fun a b => Classical.propDecidable (a = b)

local instance pointEvaluationNaturality_decidableEq_L : DecidableEq L :=
  fun a b => Classical.propDecidable (a = b)

/-- The original x coordinate commutes with the same field map. -/
theorem ptX_map (P : (E⁄K).toAffine.Point) :
    ptX (Affine.Point.map (W' := E) f P) = f (ptX P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

/-- The original y coordinate commutes with the same field map. -/
theorem ptY_map (P : (E⁄K).toAffine.Point) :
    ptY (Affine.Point.map (W' := E) f P) = f (ptY P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

/-- Lifted evaluation commutes with inclusion whenever the original point does. -/
theorem functionFieldAlgHom_comp
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hxP : Transcendental k (ptX P))
    (Q : (E⁄L).toAffine.Point) (hQ : Q ≠ 0) (hxQ : Transcendental k (ptX Q))
    (hmap : Affine.Point.map (W' := E) f P = Q) :
    f.comp (functionFieldAlgHom E P hP hxP) = functionFieldAlgHom E Q hQ hxQ := by
  apply functionFieldAlgHom_ext E
  · change f (functionFieldAlgHom E P hP hxP _) = functionFieldAlgHom E Q hQ hxQ _
    exact (congrArg f (functionFieldAlgHom_X E P hP hxP)).trans
      (((ptX_map E f P).symm.trans (congrArg ptX hmap)).trans
        (functionFieldAlgHom_X E Q hQ hxQ).symm)
  · change f (functionFieldAlgHom E P hP hxP _) = functionFieldAlgHom E Q hQ hxQ _
    exact (congrArg f (functionFieldAlgHom_Y E P hP hxP)).trans
      (((ptY_map E f P).symm.trans (congrArg ptY hmap)).trans
        (functionFieldAlgHom_Y E Q hQ hxQ).symm)

end
end JoshiTeich.Act1Scene1.WeierstrassPointEvaluationNaturality
