/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointFunctionFieldEvaluation

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-POINT-FUNCTION-FIELD-IMAGE
source: IUT I Definition 3.1(d); the same actual compatible division point,
and Mathlib's functorial group law on Weierstrass points.
fidelity: identifies the actual function-field evaluation image with the
original `QField`. The reverse inclusion descends the same division point to
the image field and uses its proved multiplication equation.
The coordinate-ring induction follows the independently ported
`ReferenceIut/Iut/Anabelian/Genuine/Basic.lean`; point descent follows
`GenuineDivisionPointTranscendence.lean`. Their source notice is retained above.
boundary: Scene1/Derived. No signed automorphism, tensor-map injectivity or
Cartesian normalization square is asserted here.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private theorem divisionPoint_coordinate_mem_QField (n : ℕ) (hn : 0 < n)
    (a : E.toAffine.CoordinateRing) :
    divisionPointFunctionFieldAlgHom E n hn
        (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField a) ∈ QField E n := by
  let f := divisionPointFunctionFieldAlgHom E n hn
  have hx : f (xF E) ∈ QField E n := by
    rw [show f (xF E) = ptX (Qpt E n) from
      divisionPointFunctionFieldAlgHom_X E n hn]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hy : f (yF E) ∈ QField E n := by
    rw [show f (yF E) = ptY (Qpt E n) from
      divisionPointFunctionFieldAlgHom_Y E n hn]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hc (c : k) : algebraMap k (Ω E) c ∈ QField E n := by
    rw [IsScalarTower.algebraMap_apply k (baseField E) (Ω E)]
    exact (QField E n).algebraMap_mem _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C q =>
    induction q using Polynomial.induction_on with
    | C c =>
      have h : f (algebraMap _ E.toAffine.FunctionField
          (AdjoinRoot.mk E.toAffine.polynomial (C (C c)))) = algebraMap k (Ω E) c := by
        change f (algebraMap _ _ (algebraMap k E.toAffine.CoordinateRing c)) = _
        rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
      rw [h]
      exact hc c
    | add q r hq hr => simpa only [C_add, map_add] using add_mem hq hr
    | monomial m c hc =>
      rw [pow_succ, ← mul_assoc, C_mul, map_mul, map_mul, map_mul]
      exact mul_mem hc hx
  | add p q hp hq => simpa only [map_add] using add_mem hp hq
  | monomial m q hq =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul]
    exact mul_mem hq hy

/-- Every value of the actual fraction-field evaluation belongs to its original division field. -/
theorem divisionPointFunctionFieldAlgHom_mem_QField (n : ℕ) (hn : 0 < n)
    (a : E.toAffine.FunctionField) :
    divisionPointFunctionFieldAlgHom E n hn a ∈ QField E n := by
  obtain ⟨b, c, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) a
  rw [map_div₀]
  exact div_mem (divisionPoint_coordinate_mem_QField E n hn b)
    (divisionPoint_coordinate_mem_QField E n hn c)

private theorem genericCoordinates_mem_of_point_coordinates_mem
    (L : IntermediateField k (Ω E))
    (P : (E⁄(Ω E)).toAffine.Point) (m : ℕ)
    (hxP : ptX P ∈ L) (hyP : ptY P ∈ L) (hPne : P ≠ 0)
    (hmul : m • P = genericPoint E) :
    xG E ∈ L ∧ yG E ∈ L := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact False.elim (hPne rfl)
  let px : L := ⟨x, hxP⟩
  let py : L := ⟨y, hyP⟩
  let ι : L →ₐ[k] Ω E := L.val
  have hnsL : (E⁄L).toAffine.Nonsingular px py := by
    exact (E.toAffine.baseChange_nonsingular (f := ι) ι.injective px py).mp hns
  let PL : (E⁄L).toAffine.Point := Affine.Point.some px py hnsL
  have hmapP : Affine.Point.map (W' := E.toAffine) ι PL =
      Affine.Point.some x y hns := by
    change Affine.Point.map (W' := E.toAffine) ι
      (Affine.Point.some px py hnsL) = _
    rw [Affine.Point.map_some]
    rfl
  have hmapMul : Affine.Point.map (W' := E.toAffine) ι (m • PL) = genericPoint E := by
    rw [map_nsmul, hmapP, hmul]
  have hxmap (Q : (E⁄L).toAffine.Point) :
      ptX (Affine.Point.map (W' := E.toAffine) ι Q) = ι (ptX Q) := by
    cases Q <;> rfl
  have hymap (Q : (E⁄L).toAffine.Point) :
      ptY (Affine.Point.map (W' := E.toAffine) ι Q) = ι (ptY Q) := by
    cases Q <;> rfl
  have hxG : xG E = ι (ptX (m • PL)) := by
    calc
      xG E = ptX (genericPoint E) := rfl
      _ = ptX (Affine.Point.map (W' := E.toAffine) ι (m • PL)) := by rw [hmapMul]
      _ = ι (ptX (m • PL)) := hxmap _
  have hyG : yG E = ι (ptY (m • PL)) := by
    calc
      yG E = ptY (genericPoint E) := rfl
      _ = ptY (Affine.Point.map (W' := E.toAffine) ι (m • PL)) := by rw [hmapMul]
      _ = ι (ptY (m • PL)) := hymap _
  constructor
  · rw [hxG]
    exact (ptX (m • PL)).property
  · rw [hyG]
    exact (ptY (m • PL)).property

private theorem divisionPointFunctionFieldRange_contains_genericCoordinates
    (n : ℕ) (hn : 0 < n) :
    xG E ∈ (divisionPointFunctionFieldAlgHom E n hn).fieldRange ∧
      yG E ∈ (divisionPointFunctionFieldAlgHom E n hn).fieldRange := by
  have hxQ : ptX (Qpt E n) ∈ (divisionPointFunctionFieldAlgHom E n hn).fieldRange :=
    ⟨xF E, divisionPointFunctionFieldAlgHom_X E n hn⟩
  have hyQ : ptY (Qpt E n) ∈ (divisionPointFunctionFieldAlgHom E n hn).fieldRange :=
    ⟨yF E, divisionPointFunctionFieldAlgHom_Y E n hn⟩
  have hQne : Qpt E n ≠ 0 := by
    rw [Qpt_eq_divSys E hn]
    exact divSys_ne_zero E n hn
  have hmul : n • Qpt E n = genericPoint E := by
    rw [Qpt_eq_divSys E hn]
    exact nsmul_divSys E n hn
  exact genericCoordinates_mem_of_point_coordinates_mem E
    (divisionPointFunctionFieldAlgHom E n hn).fieldRange (Qpt E n) n hxQ hyQ hQne hmul

/-- The range contains the original x-line base, rather than a newly supplied base embedding. -/
theorem divisionPointFunctionFieldAlgHom_baseField_le_range (n : ℕ) (hn : 0 < n) :
    baseField E ≤ (divisionPointFunctionFieldAlgHom E n hn).fieldRange := by
  rw [baseField_eq_xLine, xLine, IntermediateField.adjoin_le_iff,
    Set.singleton_subset_iff]
  exact (divisionPointFunctionFieldRange_contains_genericCoordinates E n hn).1

/-- The actual evaluation image is exactly the pre-existing division-coordinate field. -/
theorem divisionPointFunctionFieldAlgHom_fieldRange (n : ℕ) (hn : 0 < n) :
    (divisionPointFunctionFieldAlgHom E n hn).fieldRange = (QField E n).restrictScalars k := by
  let f := divisionPointFunctionFieldAlgHom E n hn
  apply le_antisymm
  · rintro z ⟨a, rfl⟩
    exact divisionPointFunctionFieldAlgHom_mem_QField E n hn a
  · let L : IntermediateField (baseField E) (Ω E) :=
      f.fieldRange.toSubfield.toIntermediateField
        (fun x => divisionPointFunctionFieldAlgHom_baseField_le_range E n hn x.2)
    have h : QField E n ≤ L := by
      rw [QField, IntermediateField.adjoin_le_iff]
      rintro z (rfl | rfl)
      · exact ⟨xF E, divisionPointFunctionFieldAlgHom_X E n hn⟩
      · exact ⟨yF E, divisionPointFunctionFieldAlgHom_Y E n hn⟩
    exact h

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
