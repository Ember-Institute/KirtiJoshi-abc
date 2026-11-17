/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation draft: exact original declaration retained; imports and surrounding
context reduced to numerical inputs. Compiler semantic identity is pending. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v w

open Finset Real



end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.log_bound_ell {δ h : ℝ} (hδ : 1 ≤ δ) (hh : 1 ≤ h) :
    Real.log (20 * δ ^ 2 * h ^ 2) ≤ 6 * Real.log (2 * δ * h) := by
  have h1 : Real.log (20 * δ ^ 2 * h ^ 2) = Real.log 20 + 2 * Real.log δ + 2 * Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have h2 : Real.log (2 * δ * h) = Real.log 2 + Real.log δ + Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h20 : Real.log 20 ≤ 6 * Real.log 2 := by
    have : Real.log 20 ≤ Real.log 64 := Real.log_le_log (by norm_num) (by norm_num)
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hδ0 : 0 ≤ Real.log δ := Real.log_nonneg hδ
  have hh0 : 0 ≤ Real.log h := Real.log_nonneg hh
  linarith
