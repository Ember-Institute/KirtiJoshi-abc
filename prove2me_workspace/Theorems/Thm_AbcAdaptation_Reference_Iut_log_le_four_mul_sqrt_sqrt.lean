/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation of the accepted reference proof at its reusable registered name;
imports and surrounding context are reduced to numerical inputs. -/
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
  set s := Real.sqrt (Real.sqrt h) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = Real.sqrt h := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs4 : s * s * (s * s) = h := by rw [hs2]; exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  have hlog : Real.log h = 4 * Real.log s := by
    rw [← hs4, show s * s * (s * s) = s ^ 4 by ring, Real.log_pow]; push_cast; ring
  rw [hlog]
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < s)
  linarith
