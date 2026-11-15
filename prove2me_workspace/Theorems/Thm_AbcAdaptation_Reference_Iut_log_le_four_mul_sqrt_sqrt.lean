/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation draft: exact original declaration retained; imports and surrounding
context reduced to numerical inputs. Compiler semantic identity is pending. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v w

open Finset Real



end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.log_le_four_mul_sqrt_sqrt {h : ℝ} (hh : 1 ≤ h) :
    Real.log h ≤ 4 * Real.sqrt (Real.sqrt h) := by
  sorry
