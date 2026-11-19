/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Source refer/iut/Iut/Implication/ChebyshevExplicit.lean, lines 91–146, 162–176,
187–192, and 205–211
Source snapshot SHA-256 3d36fd7292c87fae5c5f4a29cbabf654a4bddf7a2ca479120f291ccd1e762a20
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

/-- The lower Chebyshev bound with factor 2/3 for real arguments at least 10^12. -/
theorem two_thirds_mul_le_theta {x : ℝ} (hx : (10 : ℝ) ^ 12 ≤ x) :
    2 / 3 * x ≤ Chebyshev.theta x := by
  have hx2 : 2 ≤ x := (by norm_num : (2 : ℝ) ≤ 10 ^ 12).trans hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 2).trans hx2
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx2
  let t := Real.sqrt (Real.sqrt x)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht1000 : 1000 ≤ t := by
    have hsqrt : (10 : ℝ) ^ 6 ≤ Real.sqrt x :=
      Real.le_sqrt_of_sq_le (by
        calc
          ((10 : ℝ) ^ 6) ^ 2 = 10 ^ 12 := by norm_num
          _ ≤ x := hx)
    exact Real.le_sqrt_of_sq_le (by
      calc
        (1000 : ℝ) ^ 2 = 10 ^ 6 := by norm_num
        _ ≤ Real.sqrt x := hsqrt)
  have htpos : 0 < t := (by norm_num : (0 : ℝ) < 1000).trans_le ht1000
  have hsqrt : Real.sqrt x = t ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg x)).symm
  have hx4 : x = t ^ 4 := calc
    x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx0).symm
    _ = (t ^ 2) ^ 2 := congrArg (fun s : ℝ => s ^ 2) hsqrt
    _ = t ^ 4 := (pow_mul t 2 2).symm
  have hlogx : Real.log x ≤ 4 * t := by
    have hlog : Real.log x = 4 * Real.log t := by
      rw [hx4]
      norm_num [Real.log_pow]
    linarith only [hlog, Real.log_le_sub_one_of_pos htpos]
  have hlogx2 : Real.log (x + 2) ≤ 8 * t := by
    have hquadratic : x + 2 ≤ x ^ 2 := by
      have hproduct :=
        mul_nonneg (sub_nonneg.mpr hx2) (show 0 ≤ x + 1 by linarith only [hx2])
      nlinarith only [hproduct]
    calc
      _ ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith only [hx2]) hquadratic
      _ = 2 * Real.log x := by norm_num [Real.log_pow]
      _ ≤ 8 * t := by linarith only [hlogx]
  have hsqrtError : 2 * Real.sqrt x * Real.log x ≤ 8 * t ^ 3 := by
    rw [hsqrt]
    nlinarith only [mul_le_mul_of_nonneg_left hlogx (sq_nonneg t)]
  have hlogError : Real.log 2 + Real.log (x + 2) ≤ 8 * t ^ 3 := by
    have ht2 : 2 ≤ t := (by norm_num : (2 : ℝ) ≤ 1000).trans ht1000
    have hdiff : 0 ≤ t - 2 := sub_nonneg.mpr ht2
    have hquadratic := mul_nonneg ht0 hdiff
    have hcubic := mul_nonneg (sq_nonneg t) hdiff
    nlinarith only [Real.log_two_lt_d9, hlogx2, ht2, hquadratic, hcubic]
  -- Bound the errors in theta_ge' by the margin in its leading coefficient.
  have herror : Real.log 2 + Real.log (x + 2) + 2 * Real.sqrt x * Real.log x ≤
      0.0264 * x := by
    calc
      _ ≤ 16 * t ^ 3 := by linarith only [hlogError, hsqrtError]
      _ ≤ 0.0264 * t ^ 4 := by
        have hcoef : 16 ≤ 0.0264 * t := by linarith only [ht1000]
        nlinarith only [mul_le_mul_of_nonneg_right hcoef (pow_nonneg ht0 3)]
      _ = _ := by rw [← hx4]
  have hmain : 0.0264 * x ≤ (Real.log 2 - 2 / 3) * x :=
    mul_le_mul_of_nonneg_right (by linarith only [Real.log_two_gt_d9]) hx0
  nlinarith only [herror, hmain, Chebyshev.theta_ge' hx1]

/-- The Chebyshev certificate with threshold 10^12 and upper factor 2. -/
noncomputable def chebyshevBoundExplicit : ChebyshevBound where
  ξ := 10 ^ 12
  five_le := by norm_num
  lower _ hx := two_thirds_mul_le_theta hx
  upper x hx := by
    have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 10 ^ 12).trans hx
    have hlog : Real.log 4 ≤ 2 := by
      rw [Real.log_four_eq]
      linarith only [Real.log_two_lt_d9]
    exact (Chebyshev.theta_le_log4_mul_x hx0).trans (mul_le_mul_of_nonneg_right hlog hx0)

end AbcAdaptation.Reference.Iut
