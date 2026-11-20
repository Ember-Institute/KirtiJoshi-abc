/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/Fuchsian/Commensurator.lean and OrbicurveCores/Takeuchi.lean
-/
import Solutions.Source_ReferenceIutCanLiftFricke
import Solutions.Source_ReferenceIutCanLiftLatticeCommutatorTrace

set_option autoImplicit false

/-!
# Squared traces for the lattice generators

The lattice commutator supplies the Fricke relation for the actual edge pairings.
The first trace is nonzero, which forces all three squared traces to exceed four.
-/

open UpperHalfPlane
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Peripheral

open AbcAdaptation.Reference.Heights Generators Fricke

private theorem four_lt_sq_of_relation {x y z : ℝ}
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (hx : x ≠ 0) : 4 < x ^ 2 := by
  refine lt_of_not_ge fun hle ↦ ?_
  have habs : |x| ≤ 2 := abs_le_of_sq_le_sq (by norm_num <;> exact hle) (by norm_num)
  have hproduct : x * y * z ≤ |x| * (|y| * |z|) := by
    simpa only [abs_mul, mul_assoc] using le_abs_self (x * y * z)
  have hmul : |x| * (|y| * |z|) ≤ 2 * (|y| * |z|) :=
    mul_le_mul_of_nonneg_right habs (mul_nonneg (abs_nonneg y) (abs_nonneg z))
  have hsum : 2 * (|y| * |z|) ≤ y ^ 2 + z ^ 2 := by
    nlinarith only [sq_nonneg (|y| - |z|), sq_abs y, sq_abs z]
  have hbound := hproduct.trans (hmul.trans hsum)
  linarith only [hrel, hbound, sq_pos_of_ne_zero hx]

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))

/-- The two edge pairings and their product satisfy the Fricke relation. -/
theorem fricke_trace_relation :
    tr (A U) ^ 2 + tr (B U) ^ 2 + tr (A U * B U) ^ 2 =
      tr (A U) * tr (B U) * tr (A U * B U) :=
  (tr_commutator_eq_neg_two_iff (A U) (B U)).mp (trace_commutator U)

/-- All three squared traces of the lattice edge pairings exceed four. -/
theorem traces_sq_gt_four :
    4 < tr (A U) ^ 2 ∧ 4 < tr (B U) ^ 2 ∧ 4 < tr (A U * B U) ^ 2 := by
  set x := tr (A U)
  set y := tr (B U)
  set z := tr (A U * B U)
  have hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z := fricke_trace_relation U
  have hx : x ≠ 0 := trace_A_ne_zero U
  have hpos : 0 < x ^ 2 + y ^ 2 + z ^ 2 :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y))
      (sq_nonneg z)
  rw [hrel] at hpos
  obtain ⟨hxy, hz⟩ := mul_ne_zero_iff.mp (ne_of_gt hpos)
  have hy := (mul_ne_zero_iff.mp hxy).2
  exact ⟨four_lt_sq_of_relation hrel hx,
    four_lt_sq_of_relation (y := x) (z := z) (by linear_combination hrel) hy,
    four_lt_sq_of_relation (y := x) (z := y) (by linear_combination hrel) hz⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Peripheral
