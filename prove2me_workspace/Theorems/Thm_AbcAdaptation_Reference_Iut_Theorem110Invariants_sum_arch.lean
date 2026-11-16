/- Adapted complete original proof. Source: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Theorem110.lean#L157-L166
Original authors: The iut contributors; Apache-2.0. Only the declaration binding, namespace and imports are adapted. -/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators

namespace AbcAdaptation.Reference
namespace Iut.Theorem110Invariants
/-- The sum over the capsules of the archimedean bound `(j+1)·log π`, via (E1). -/
lemma sum_arch (L : ℕ) :
    ∑ i : Fin L, (((i : ℕ) + 2 : ℕ) : ℝ) * Real.log Real.pi =
      Real.log Real.pi * (L * (L + 3) / 2) := by
  have := sum_affine_quadratic L (Real.log Real.pi) 0 0
  simp only [zero_mul, add_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

end Iut.Theorem110Invariants
end AbcAdaptation.Reference
