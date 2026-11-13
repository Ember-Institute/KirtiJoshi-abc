/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of Belyi/CurveField/Divisor.lean:190-213
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The Model, Place, normalized ord, residue degree, and function divisors are
exactly the existing carriers. No second divisor structure is introduced.
-/
import Definitions.Def_FermatFunctionDivisors
import Definitions.Def_FermatCurveFieldDegree

set_option autoImplicit false

open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

theorem divisorDegree_eq_sum_of_support_subset (M : Model N) (A : Divisor M)
    {s : Finset (Place M.K)} (hs : A.support ⊆ s) :
    divisorDegree M A = ∑ P ∈ s, A P * (P.degree : ℤ) :=
  Finsupp.sum_of_support_subset A hs _ fun _ _ => zero_mul _

/-- The zero fiber has its actual function-field extension degree. -/
theorem functionZeroDivisor_degree (M : Model N) (hDVR : PlacesDiscrete M)
    {f : M.K} (hf : Transcendental ℚ f) :
    divisorDegree M (functionZeroDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  rw [← Place.sum_ord_mul_deg_zeros f hf,
    divisorDegree_eq_sum_of_support_subset M (functionZeroDivisor M hDVR f)
      (s := (Place.finite_setOf_ord_pos f).toFinset)]
  · refine Finset.sum_congr rfl fun P hP => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    rw [functionZeroDivisor_apply, ord_eq_placeOrd, max_eq_right hP.le]
  · intro P hP
    rw [Finsupp.mem_support_iff, functionZeroDivisor_apply, ord_eq_placeOrd] at hP
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega

/-- The pole fiber includes every proper place, through the chart for f⁻¹. -/
theorem functionPoleDivisor_degree (M : Model N) (hDVR : PlacesDiscrete M)
    {f : M.K} (hf : Transcendental ℚ f) :
    divisorDegree M (functionPoleDivisor M hDVR f) =
      (Module.finrank ℚ⟮f⟯ M.K : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  rw [← Place.sum_ord_mul_deg_poles f hf,
    divisorDegree_eq_sum_of_support_subset M (functionPoleDivisor M hDVR f)
      (s := (Place.finite_setOf_ord_neg f).toFinset)]
  · refine Finset.sum_congr rfl fun P hP => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    rw [functionPoleDivisor_apply, ord_eq_placeOrd, max_eq_right (by omega)]
  · intro P hP
    rw [Finsupp.mem_support_iff, functionPoleDivisor_apply, ord_eq_placeOrd] at hP
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega

end AbcAdaptation.Tripod.Fermat.Proper
