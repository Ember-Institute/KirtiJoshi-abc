/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Solutions.Source_ReferenceIutCanLiftCommensuratorIndex
import Solutions.Source_ReferenceIutCanLiftDenseUnipotents
import Solutions.Source_ReferenceIutCanLiftFrickeComplexAction

set_option autoImplicit false

open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

lemma neg_one_mem_commensurator (Γ : Subgroup SL(2, ℝ)) : (-1 : SL(2, ℝ)) ∈ commensurator Γ := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct (-1 : SL(2, ℝ)) • Γ = Γ := by
    ext g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
    simp
  rw [this]

open Fricke (nA nB)

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

lemma uU_two_eq : SL2R.uU 2 = -1 * commK hz hrel := by
  ext i j
  rw [SL2R.coe_uU, Matrix.SpecialLinearGroup.coe_mul, coe_commK,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_mul, one_mul]
  fin_cases i <;> fin_cases j <;> simp

/-- The upper unipotent with parameter two belongs to the commensurator of the normal form. -/
lemma uU_two_mem_commensurator :
    SL2R.uU 2 ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  rw [uU_two_eq hz hrel]
  exact mul_mem (neg_one_mem_commensurator _) (le_commensurator _ (commK_mem hz hrel))

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
