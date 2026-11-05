/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointFunctionFieldImage
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineFunctionFieldNegation

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-FIELD-NEGATION
source: IUT I Definition 3.1(d); the actual chosen compatible division point;
Mathlib `AlgHom.equivFieldRange` and `IntermediateField.equivOfEq`.
fidelity: uses the proved evaluation-image identity to transport the original
function-field involution to the pre-existing `QField E n`, retaining its
inclusion in the same `Ω E` and the same chosen division-point coordinates.
No new reference-project code is copied.
boundary: Scene1/Derived. This does not yet extend the automorphism to `Ω E`,
construct a signed-group witness or prove the Cartesian normalization square.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

/-- The original function field is isomorphic to the actual division field. -/
def divisionPointFunctionFieldEquiv (n : ℕ) (hn : 0 < n) :
    E.toAffine.FunctionField ≃ₐ[k] QField E n :=
  (divisionPointFunctionFieldAlgHom E n hn).equivFieldRange.trans
    (IntermediateField.equivOfEq (divisionPointFunctionFieldAlgHom_fieldRange E n hn))

/-- The equivalence retains the original evaluation into the same ambient closure. -/
@[simp] theorem coe_divisionPointFunctionFieldEquiv (n : ℕ) (hn : 0 < n)
    (a : E.toAffine.FunctionField) :
    ((divisionPointFunctionFieldEquiv E n hn a : QField E n) : Ω E) =
      divisionPointFunctionFieldAlgHom E n hn a := by
  rfl

/-- Negation transported to the same actual division-coordinate field. -/
def divisionFieldNegationEquiv (n : ℕ) (hn : 0 < n) :
    QField E n ≃ₐ[k] QField E n :=
  (divisionPointFunctionFieldEquiv E n hn).symm.trans
    ((functionFieldNegationEquiv E).trans (divisionPointFunctionFieldEquiv E n hn))

/-- Actual evaluation intertwines the two original negation maps. -/
@[simp] theorem divisionFieldNegationEquiv_apply_equiv (n : ℕ) (hn : 0 < n)
    (a : E.toAffine.FunctionField) :
    divisionFieldNegationEquiv E n hn (divisionPointFunctionFieldEquiv E n hn a) =
      divisionPointFunctionFieldEquiv E n hn (functionFieldNegationEquiv E a) := by
  simp only [divisionFieldNegationEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- Inclusion in the original closure commutes with the transported formula. -/
theorem coe_divisionFieldNegationEquiv (n : ℕ) (hn : 0 < n) (a : QField E n) :
    ((divisionFieldNegationEquiv E n hn a : QField E n) : Ω E) =
      divisionPointFunctionFieldAlgHom E n hn
        (functionFieldNegationEquiv E ((divisionPointFunctionFieldEquiv E n hn).symm a)) := by
  change ((divisionPointFunctionFieldEquiv E n hn
    (functionFieldNegationEquiv E ((divisionPointFunctionFieldEquiv E n hn).symm a)) :
      QField E n) : Ω E) = _
  exact coe_divisionPointFunctionFieldEquiv E n hn _

private theorem divisionPoint_X_mem_QField (n : ℕ) : ptX (Qpt E n) ∈ QField E n :=
  IntermediateField.subset_adjoin _ _ (by simp)

private theorem divisionPoint_Y_mem_QField (n : ℕ) : ptY (Qpt E n) ∈ QField E n :=
  IntermediateField.subset_adjoin _ _ (by simp)

/-- The x-coordinate of the same actual chosen division point is fixed. -/
@[simp] theorem divisionFieldNegationEquiv_X (n : ℕ) (hn : 0 < n) :
    ((divisionFieldNegationEquiv E n hn
      ⟨ptX (Qpt E n), divisionPoint_X_mem_QField E n⟩ : QField E n) : Ω E) =
        ptX (Qpt E n) := by
  have hx : divisionPointFunctionFieldEquiv E n hn (xF E) =
      (⟨ptX (Qpt E n), divisionPoint_X_mem_QField E n⟩ : QField E n) := by
    apply Subtype.ext
    rw [coe_divisionPointFunctionFieldEquiv]
    exact divisionPointFunctionFieldAlgHom_X E n hn
  rw [← hx, divisionFieldNegationEquiv_apply_equiv, functionFieldNegationEquiv_xF,
    coe_divisionPointFunctionFieldEquiv]
  exact divisionPointFunctionFieldAlgHom_X E n hn

/-- The actual chosen y-coordinate has the original affine negation formula. -/
@[simp] theorem divisionFieldNegationEquiv_Y (n : ℕ) (hn : 0 < n) :
    ((divisionFieldNegationEquiv E n hn
      ⟨ptY (Qpt E n), divisionPoint_Y_mem_QField E n⟩ : QField E n) : Ω E) =
        -ptY (Qpt E n) - algebraMap k (Ω E) E.a₁ * ptX (Qpt E n) -
          algebraMap k (Ω E) E.a₃ := by
  have hxEval : divisionPointFunctionFieldAlgHom E n hn (xF E) = ptX (Qpt E n) :=
    divisionPointFunctionFieldAlgHom_X E n hn
  have hyEval : divisionPointFunctionFieldAlgHom E n hn (yF E) = ptY (Qpt E n) :=
    divisionPointFunctionFieldAlgHom_Y E n hn
  have hy : divisionPointFunctionFieldEquiv E n hn (yF E) =
      (⟨ptY (Qpt E n), divisionPoint_Y_mem_QField E n⟩ : QField E n) := by
    apply Subtype.ext
    rw [coe_divisionPointFunctionFieldEquiv]
    exact hyEval
  rw [← hy, divisionFieldNegationEquiv_apply_equiv, coe_divisionPointFunctionFieldEquiv,
    functionFieldNegationEquiv_yF]
  simp only [map_sub, map_neg, map_mul, AlgHom.commutes, hxEval, hyEval]

/-- The transported automorphism is involutive on the original division field. -/
theorem divisionFieldNegationEquiv_involutive (n : ℕ) (hn : 0 < n) :
    Function.Involutive (divisionFieldNegationEquiv E n hn) := by
  intro a
  obtain ⟨z, rfl⟩ := (divisionPointFunctionFieldEquiv E n hn).surjective a
  rw [divisionFieldNegationEquiv_apply_equiv, divisionFieldNegationEquiv_apply_equiv]
  exact congrArg (divisionPointFunctionFieldEquiv E n hn)
    (functionFieldNegationEquiv_involutive E z)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
