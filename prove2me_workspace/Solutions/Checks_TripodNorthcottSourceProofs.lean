import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness

set_option autoImplicit false

-- Explicit type checks; this source is only a candidate for main-agent MCP-CI.
example : AbcAdaptation.Tripod.Northcott.FiniteRoots :=
  AbcAdaptation.Tripod.northcottFiniteRoots
example : AbcAdaptation.Tripod.Northcott.PolynomialWitness :=
  AbcAdaptation.Tripod.northcottPolynomialWitness
example : ∀ (d : ℕ) (H : ℝ),
    {x : AbcAdaptation.Tripod.Pt |
      AbcAdaptation.Tripod.deg x.1 ≤ d ∧ AbcAdaptation.Tripod.htCan x ≤ H}.Finite :=
  AbcAdaptation.Tripod.boundedDegreeFiniteness

#print axioms AbcAdaptation.Tripod.Northcott.norm_embedding_le_mulHeight_one
#print axioms AbcAdaptation.Tripod.Northcott.mulHeight_one_gen_le
#print axioms AbcAdaptation.Tripod.Northcott.natDegree_minpoly_int_le
#print axioms AbcAdaptation.Tripod.Northcott.coeff_minpoly_int_mem_Icc
#print axioms AbcAdaptation.Tripod.Northcott.eval₂_minpoly_int_algebraMap
#print axioms AbcAdaptation.Tripod.northcottFiniteRoots
#print axioms AbcAdaptation.Tripod.northcottPolynomialWitness
#print axioms AbcAdaptation.Tripod.boundedDegreeFiniteness_of_northcott_children
#print axioms AbcAdaptation.Tripod.boundedDegreeFiniteness
