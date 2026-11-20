/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fricke.lean
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
# Fricke trace identities

The trace of a commutator in `SL(2, R)` is a polynomial in the traces of its two factors
and their product. A commutator of trace `-2` therefore puts these three traces on the
Fricke surface. Inverting the first factor replaces the third trace by the other root
of the equation in that coordinate.
-/

open Matrix
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke

variable {R : Type*} [CommRing R]

/-- The trace of a determinant-one two-by-two matrix. -/
abbrev tr (A : SL(2, R)) : R := Matrix.trace (A : Matrix (Fin 2) (Fin 2) R)

private theorem det_eq (A : SL(2, R)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.det_coe
  rwa [Matrix.det_fin_two] at h

theorem tr_def (A : SL(2, R)) : tr A = A 0 0 + A 1 1 := by
  simp [tr, trace_fin_two]

@[simp]
theorem tr_one : tr (1 : SL(2, R)) = 2 := by
  simp [tr_def] <;> norm_num

theorem tr_inv (A : SL(2, R)) : tr A⁻¹ = tr A := by
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two] <;> ring

theorem tr_mul_comm (A B : SL(2, R)) : tr (A * B) = tr (B * A) := by
  simp only [tr, Matrix.SpecialLinearGroup.coe_mul]
  exact trace_mul_comm _ _

/-- Inverting the first generator performs the Vieta move on the product trace. -/
theorem tr_inv_mul (A B : SL(2, R)) : tr (A⁻¹ * B) = tr A * tr B - tr (A * B) := by
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, mul_apply,
    Fin.sum_univ_two] <;> ring

theorem tr_mul_mul_self (A B : SL(2, R)) :
    tr (A * (A * B)) = tr A * tr (A * B) - tr B := by
  have hA := det_eq A
  simp [tr_def, mul_apply, Fin.sum_univ_two]
  linear_combination (-(B 0 0) - B 1 1) * hA

/-- Fricke's trace identity for the commutator in the order used by CanLift. -/
theorem tr_commutator (A B : SL(2, R)) :
    tr (A * B * A⁻¹ * B⁻¹) =
      tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 - tr A * tr B * tr (A * B) - 2 := by
  have hA := det_eq A
  have hB := det_eq B
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, mul_apply,
    Fin.sum_univ_two]
  linear_combination
    ((B 0 0 + B 1 1) ^ 2 - 2 * (B 0 0 * B 1 1 - B 0 1 * B 1 0)) * hA +
      ((A 0 0 + A 1 1) ^ 2 - 2) * hB

/-- For a commutator of trace `-2`, the sum of the three squares is the product of the traces. -/
theorem tr_commutator_eq_neg_two_iff (A B : SL(2, R)) :
    tr (A * B * A⁻¹ * B⁻¹) = -2 ↔
      tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 = tr A * tr B * tr (A * B) := by
  rw [tr_commutator]
  constructor <;> intro h <;> linear_combination h

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke
