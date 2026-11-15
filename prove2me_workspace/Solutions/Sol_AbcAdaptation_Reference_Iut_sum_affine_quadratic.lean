/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation draft: exact original declaration retained; imports and surrounding
context reduced to numerical inputs. Compiler semantic identity is pending. -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v



end Iut

end AbcAdaptation.Reference

theorem solution (L : ℕ) (a b c : ℝ) :
    ∑ i : Fin L, (a * ((i : ℝ) + 2) + b * ((i : ℝ) + 1) ^ 2 + c) =
      a * (L * (L + 3) / 2) + b * (L * (L + 1) * (2 * L + 1) / 6) + c * L := by
  rw [Fin.sum_univ_eq_sum_range (fun i => a * ((i : ℝ) + 2) + b * ((i : ℝ) + 1) ^ 2 + c) L]
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
