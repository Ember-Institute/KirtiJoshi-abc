/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/GoodLattice.lean
-/
import Solutions.Source_ReferenceIutCanLiftFrickeDiscreteness
import Solutions.Source_ReferenceIutCanLiftFrickeStripCover
import Solutions.Source_ReferenceIutCanLiftGoodLatticeBasic

set_option autoImplicit false

open MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The positive Fricke normal-form group is a good lattice under the triangle inequalities. -/
theorem goodLattice_normal (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y) : GoodLattice (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  haveI hdisc : DiscreteTopology Γ := discreteTopology_normal hx hy hz hrel
  obtain ⟨η, hη, hcov⟩ := exists_strip_cover_normal hz hrel hx hy h1 h2 h3
  have hA : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  set K := nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹
  have hK : K ∈ Γ := mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
  have hKmat : (K : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -2; 0, -1] :=
    coe_commutator_n hz hrel
  have hK2 : ((K * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 4; 0, 1] := by
    rw [coe_mul, hKmat]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hdisc, _, (measurableSet_Icc.preimage continuous_re.measurable).inter
    (measurableSet_Ici.preimage continuous_im.measurable), volume_strip_lt_top _ _ _ hη, hcov,
    fun w ↦ ?_⟩
  exact finite_strip_multiplicity (mul_mem hK hK) (by norm_num) hK2 _ _ η hη w

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
