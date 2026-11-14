/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3



namespace Iut

universe u v













/-- The final numerical bookkeeping of Step (viii), as an inequality between real numbers.
The hypotheses are: `h1`, the summed local bound after substitution of Corollary 3.12
(cleared of denominators); `h2`, `h3`, Steps (ii) and (iii); `h4`, the Proposition 1.6
bound. -/
lemma assembly {ℓ d D Q S T P DF E e lg : ℝ} (hℓ : 7 ≤ ℓ) (hd : 1 ≤ d) (_hD : 0 ≤ D)
    (_hQ : 0 ≤ Q) (_hS : 0 ≤ S) (_hT : 0 ≤ T) (_hP0 : 0 ≤ P) (hP : P ≤ 2) (hDF : 0 ≤ DF)
    (_hlg0 : 0 ≤ lg) (hlg : lg ≤ ℓ) (he : 552960 * ℓ ≤ e) (hE : e ≤ E)
    (h1 : -12 * Q ≤ 6 * ℓ * (ℓ + 5) * D - ℓ * (ℓ + 1) * Q + 24 * ℓ * S +
      24 * ℓ * (ℓ + 5) * T + 6 * ℓ * (ℓ + 5) * P)
    (h2 : D ≤ DF + 2 * lg + 21) (h3 : S ≤ 2 * d * DF + 5 + lg) (h4 : 2 * T ≤ 3 * E) :
    ℓ * Q ≤ 6 * (ℓ + 20 * d) * DF + 120 * ℓ * E := by
  have hE0 : 0 ≤ E := by linarith
  have hℓ5 : 0 ≤ ℓ + 5 := by linarith
  -- the bracket `B` of the local bounds and its estimate `B'`
  set B : ℝ := (ℓ + 5) * D + 4 * S + 4 * (ℓ + 5) * T + (ℓ + 5) * P with hB
  have step1 : (ℓ ^ 2 + ℓ - 12) * Q ≤ 6 * ℓ * B := by rw [hB]; nlinarith
  have hB' : B ≤ (ℓ + 5 + 8 * d) * DF + (2 * ℓ + 14) * lg + 23 * ℓ + 135 +
      6 * (ℓ + 5) * E := by
    rw [hB]
    nlinarith [mul_le_mul_of_nonneg_left h2 hℓ5, mul_le_mul_of_nonneg_left h4 hℓ5,
      mul_le_mul_of_nonneg_left hP hℓ5]
  have hpos : 0 < ℓ ^ 2 + ℓ - 12 := by nlinarith
  -- the polynomial comparison of the two sides
  have hpoly : 6 * ℓ ^ 2 * ((ℓ + 5 + 8 * d) * DF + (2 * ℓ + 14) * lg + 23 * ℓ + 135 +
      6 * (ℓ + 5) * E) ≤ (ℓ ^ 2 + ℓ - 12) * (6 * (ℓ + 20 * d) * DF + 120 * ℓ * E) := by
    have hDFc : 6 * ℓ ^ 2 * (ℓ + 5 + 8 * d) * DF ≤ (ℓ ^ 2 + ℓ - 12) * (6 * (ℓ + 20 * d)) * DF := by
      apply mul_le_mul_of_nonneg_right _ hDF
      nlinarith [mul_nonneg (sub_nonneg.2 hd) (show (0:ℝ) ≤ 12 * ℓ ^ 2 + 20 * ℓ - 240 by nlinarith),
        mul_le_mul hℓ hℓ (by norm_num) (by linarith)]
    have hrest : 6 * ℓ ^ 2 * ((2 * ℓ + 14) * lg + 23 * ℓ + 135 + 6 * (ℓ + 5) * E) ≤
        (ℓ ^ 2 + ℓ - 12) * (120 * ℓ * E) := by
      have hlg' : (2 * ℓ + 14) * lg + 23 * ℓ + 135 ≤ 63 * ℓ ^ 2 := by nlinarith
      have he' : 63 * ℓ ^ 2 ≤ ℓ * E / 8000 := by nlinarith
      have hA : 6 * ℓ ^ 2 * ((2 * ℓ + 14) * lg + 23 * ℓ + 135) ≤ 6 * ℓ ^ 2 * (ℓ * E / 8000) :=
        mul_le_mul_of_nonneg_left (hlg'.trans he') (by positivity)
      have hpoly' : 0 ≤ ℓ * E * (83 * ℓ ^ 2 - 60 * ℓ - 1440) :=
        mul_nonneg (mul_nonneg (by linarith) hE0) (by nlinarith)
      have hcube : 0 ≤ ℓ ^ 3 * E := by positivity
      nlinarith [hA, hpoly', hcube]
    nlinarith
  have step2 : (ℓ ^ 2 + ℓ - 12) * (ℓ * Q) ≤
      (ℓ ^ 2 + ℓ - 12) * (6 * (ℓ + 20 * d) * DF + 120 * ℓ * E) := by
    calc (ℓ ^ 2 + ℓ - 12) * (ℓ * Q) = ℓ * ((ℓ ^ 2 + ℓ - 12) * Q) := by ring
      _ ≤ ℓ * (6 * ℓ * B) := mul_le_mul_of_nonneg_left step1 (by linarith)
      _ = 6 * ℓ ^ 2 * B := by ring
      _ ≤ 6 * ℓ ^ 2 * ((ℓ + 5 + 8 * d) * DF + (2 * ℓ + 14) * lg + 23 * ℓ + 135 +
          6 * (ℓ + 5) * E) := mul_le_mul_of_nonneg_left hB' (by positivity)
      _ ≤ _ := hpoly
  exact le_of_mul_le_mul_left step2 hpos



















end Iut
