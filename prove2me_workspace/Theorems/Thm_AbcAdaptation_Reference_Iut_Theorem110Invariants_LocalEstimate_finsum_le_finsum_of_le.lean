/- Adapted complete original proof. Source: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/LogVolumeBound.lean#L149-L158
Original authors: The iut contributors; Apache-2.0. Only the declaration binding, namespace and imports are adapted. -/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lattice

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators

namespace AbcAdaptation.Reference
namespace Iut.Theorem110Invariants.LocalEstimate
/-- A finite sum dominated pointwise by a finitely supported function is dominated by
its sum. -/
lemma finsum_le_finsum_of_le {α : Type*} {f g : α → ℝ} (h : ∀ a, f a ≤ g a)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  rw [finsum_eq_sum_of_support_subset f (s := (hf.union hg).toFinset) (by
      intro a ha; simp only [Set.Finite.coe_toFinset]; exact Or.inl ha),
    finsum_eq_sum_of_support_subset g (s := (hf.union hg).toFinset) (by
      intro a ha; simp only [Set.Finite.coe_toFinset]; exact Or.inr ha)]
  exact Finset.sum_le_sum fun a _ => h a

end Iut.Theorem110Invariants.LocalEstimate
end AbcAdaptation.Reference
