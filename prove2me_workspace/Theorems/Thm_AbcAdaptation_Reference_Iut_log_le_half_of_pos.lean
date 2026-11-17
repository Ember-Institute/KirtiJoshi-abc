/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation draft: exact original declaration retained; imports and surrounding
context reduced to numerical inputs. Compiler semantic identity is pending. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v w

open Finset Real



end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.log_le_half_of_pos {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  set s := Real.sqrt y with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hy
  have hss : s * s = y := Real.mul_self_sqrt hy.le
  have h1 : Real.log y = 2 * Real.log s := by
    rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
  have h2 := Real.log_le_sub_one_of_pos hs0
  have h3 : s ≤ y / 4 + 1 := by nlinarith [sq_nonneg (s - 2)]
  linarith
