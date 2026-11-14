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

universe u v w





















/-- The final arithmetic of Corollary 2.2(ii): from Theorem 1.10 (`h110`), the comparison
of `log(q_∀)` with `log(q)` (`hlogQ`), and the bounds (P1) on `ℓ`, derive (C2) with
`ε_E = (60δ)²·log(2δh)/√h ≤ 1` and `C_K = 40η + B/3`. -/
lemma c2_final {h r lg δ ℓ dm e D F LD LC Q B η ε : ℝ}
    (hr0 : 0 < r) (hrr : r * r = h) (hlg1 : 1 ≤ lg) (hδ1 : 1 ≤ δ)
    (hℓlo : r ≤ ℓ) (hℓhi : ℓ ≤ 10 * δ * r * lg)
    (hdm : 20 * dm ≤ δ) (he : e ≤ δ) (hDF0 : 0 ≤ D + F) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (h110 : 1 / 6 * Q ≤ (1 + 20 * dm / ℓ) * (D + F) + 20 * (e * ℓ + η))
    (hlogQ : h ≤ Q + B + 6 * (r * lg))
    (hD : LD = D) (hF : F ≤ LC)
    (hε : ε = (60 * δ) ^ 2 * lg / r) (hε1 : ε ≤ 1) :
    1 / 6 * h ≤ (1 + ε) * (LD + LC) + (40 * η + B / 3) := by
  have hℓpos : 0 < ℓ := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hrlg : 0 ≤ r * lg := by positivity
  have hεr : ε * r = (60 * δ) ^ 2 * lg := by rw [hε, div_mul_cancel₀ _ hr0.ne']
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  -- `20·dm/ℓ ≤ δ/r`
  have hcoef : 20 * dm / ℓ ≤ δ / r := by
    rw [div_le_div_iff₀ hℓpos hr0]
    nlinarith [mul_le_mul_of_nonneg_right hdm hr0.le,
      mul_le_mul_of_nonneg_left hℓlo (by linarith : 0 ≤ δ)]
  -- Theorem 1.10 in the form `(1/6)Q ≤ (1 + δ/r)(D+F) + 200δ²·r·lg + 20η`
  have h110' : 1 / 6 * Q ≤ (1 + δ / r) * (D + F) + 200 * δ ^ 2 * (r * lg) + 20 * η := by
    have h1 : (1 + 20 * dm / ℓ) * (D + F) ≤ (1 + δ / r) * (D + F) :=
      mul_le_mul_of_nonneg_right (by linarith) hDF0
    have h2 : e * ℓ ≤ δ * (10 * δ * r * lg) := mul_le_mul he hℓhi hℓpos.le (by linarith)
    nlinarith
  -- `δ/r ≤ ε/5` and `(200δ² + 1)·r·lg ≤ (2/5)·ε·(h/6)`
  have hδr : δ / r ≤ ε / 5 := by
    rw [div_le_iff₀ hr0]
    have : ε / 5 * r = (60 * δ) ^ 2 * lg / 5 := by rw [← hεr]; ring
    rw [this]
    nlinarith
  have hbig : (200 * δ ^ 2 + 1) * (r * lg) ≤ 2 / 5 * ε * (h / 6) := by
    have : 2 / 5 * ε * (h / 6) = (2 / 5) * (ε * r) * r / 6 := by rw [← hrr]; ring
    rw [this, hεr]
    nlinarith
  -- `(1 − 2ε/5)(h/6) ≤ (1 + ε/5)(D+F) + (20η + B/6)`
  have hstep : (1 - 2 / 5 * ε) * (h / 6) ≤ (1 + ε / 5) * (D + F) + (20 * η + B / 6) := by
    have h1 : (1 + δ / r) * (D + F) ≤ (1 + ε / 5) * (D + F) :=
      mul_le_mul_of_nonneg_right (by linarith) hDF0
    nlinarith
  -- `(1+ε/5)/(1−2ε/5) ≤ 1 + ε` and `1/(1−2ε/5) ≤ 2` for `0 ≤ ε ≤ 1`
  have hden : 3 / 5 ≤ 1 - 2 / 5 * ε := by linarith
  have hεε : ε * ε ≤ ε := mul_le_of_le_one_left hε0 hε1
  have hfrac : (1 + ε / 5) * (D + F) ≤ (1 - 2 / 5 * ε) * ((1 + ε) * (D + F)) := by
    have h1 : (1 + ε / 5) ≤ (1 - 2 / 5 * ε) * (1 + ε) := by linarith
    have := mul_le_mul_of_nonneg_right h1 hDF0
    linarith
  have hconst : 20 * η + B / 6 ≤ (1 - 2 / 5 * ε) * (40 * η + B / 3) := by
    have h1 : ε * η ≤ η := mul_le_of_le_one_left hη hε1
    have h2 : ε * B ≤ B := mul_le_of_le_one_left hB hε1
    linarith
  have hall : (1 - 2 / 5 * ε) * (h / 6) ≤
      (1 - 2 / 5 * ε) * ((1 + ε) * (D + F) + (40 * η + B / 3)) := by linarith
  have hfin := le_of_mul_le_mul_left hall (by linarith)
  have hmono : (1 + ε) * (D + F) ≤ (1 + ε) * (LD + LC) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  linarith
























end Iut
