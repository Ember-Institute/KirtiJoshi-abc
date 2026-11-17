/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation draft: exact original declaration retained; imports and surrounding
context reduced to numerical inputs. Compiler semantic identity is pending. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v



end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.log_pi_le_two : Real.log Real.pi ≤ 2 := by
  have h4 : Real.log Real.pi ≤ Real.log 4 :=
    Real.log_le_log Real.pi_pos Real.pi_le_four
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  linarith
