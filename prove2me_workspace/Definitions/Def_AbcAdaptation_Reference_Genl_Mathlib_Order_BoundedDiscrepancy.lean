/- Adaptation draft: two complete original relation definitions and their two original notation commands. Mathematical bodies and context are unchanged. Original source notice retained. No source theorem or Open proof is imported. -/
/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference


variable {α β : Type*}

/-- `DiscrepancyLE f g s`, denoted `f ≲[s] g`, means that `f` is bounded above by `g` up
to a bounded discrepancy on `s`, i.e. there exists a constant `C` such that
`f x ≤ g x + C` for all `x ∈ s`. -/
def DiscrepancyLE (f g : α → ℝ) (s : Set α) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, f x ≤ g x + C

/-- `DiscrepancyEquiv f g s`, denoted `f ≈[s] g`, means that `f` and `g` agree up to a
bounded discrepancy on `s`, i.e. `|f x - g x|` is bounded on `s`. The equivalence classes
of this relation are called *BD-classes*. -/
def DiscrepancyEquiv (f g : α → ℝ) (s : Set α) : Prop :=
  DiscrepancyLE f g s ∧ DiscrepancyLE g f s

@[inherit_doc]
notation:50 f:51 " ≲[" s "] " g:51 => DiscrepancyLE f g s

@[inherit_doc]
notation:50 f:51 " ≈[" s "] " g:51 => DiscrepancyEquiv f g s

end AbcAdaptation.Reference
