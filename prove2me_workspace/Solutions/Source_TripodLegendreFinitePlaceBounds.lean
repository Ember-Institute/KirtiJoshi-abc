/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:439-486.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/
import Solutions.Source_TripodLegendreValuationBounds
import Solutions.Source_TripodFinitePlaceArithmetic

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

variable {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) {l : T}
  (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- The three terms of the comparison at a finite place, in terms of the valuation. -/
lemma posLog_terms_eq :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) =
      finWeight w * (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [posLog_apply_eq w hl0, posLog_apply_eq w (inv_ne_zero hl0),
    posLog_apply_eq w (inv_ne_zero hl1'), map_inv₀, map_inv₀, log_inv, log_inv]
  unfold legendreBound
  push_cast
  ring

/-- **`log⁺|j|_w ≤ 2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w)`** at every finite place. -/
theorem posLog_legendreJ_le :
    log⁺ (w (legendreJ l)) ≤ 2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) := by
  rw [posLog_terms_eq w hl0 hl1]
  by_cases hj : legendreJ l = 0
  · rw [hj, map_zero, Real.posLog_zero]
    exact mul_nonneg (finWeight_pos w).le (by exact_mod_cast legendreBound_nonneg _ l)
  rw [posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h := max_log_valuation_legendreJ_le (w.maximalIdeal.valuation T) hl0 hl1
    (valuation_256_le_one w)
  have h' : ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) ≤
      (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

/-- **`2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w) ≤ log⁺|j|_w`** at a finite place of odd
residue characteristic, for `j ≠ 0`. -/
theorem posLog_legendreJ_ge (h2 : residueChar w ≠ 2) (hj : legendreJ l ≠ 0) :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) ≤ log⁺ (w (legendreJ l)) := by
  rw [posLog_terms_eq w hl0 hl1, posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h256 : w.maximalIdeal.valuation T 256 = 1 := by
    have : (256 : T) = 2 ^ 8 := by norm_num
    rw [this, map_pow, valuation_two_eq_one_of_ne h2, one_pow]
  have h := legendreBound_le_max_log_valuation_legendreJ (w.maximalIdeal.valuation T) hl0 hl1
    h256 ((Valuation.ne_zero_iff _).mpr hj)
  have h' : (legendreBound (w.maximalIdeal.valuation T) l : ℝ) ≤
      ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

end AbcAdaptation.Tripod
