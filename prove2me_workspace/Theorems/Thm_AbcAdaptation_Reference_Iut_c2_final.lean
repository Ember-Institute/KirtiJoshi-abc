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

namespace AbcAdaptation.Reference



set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3



namespace Iut

universe u v w














































end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.c2_final {h r lg δ ℓ dm e D F LD LC Q B η ε : ℝ}
    (hr0 : 0 < r) (hrr : r * r = h) (hlg1 : 1 ≤ lg) (hδ1 : 1 ≤ δ)
    (hℓlo : r ≤ ℓ) (hℓhi : ℓ ≤ 10 * δ * r * lg)
    (hdm : 20 * dm ≤ δ) (he : e ≤ δ) (hDF0 : 0 ≤ D + F) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (h110 : 1 / 6 * Q ≤ (1 + 20 * dm / ℓ) * (D + F) + 20 * (e * ℓ + η))
    (hlogQ : h ≤ Q + B + 6 * (r * lg))
    (hD : LD = D) (hF : F ≤ LC)
    (hε : ε = (60 * δ) ^ 2 * lg / r) (hε1 : ε ≤ 1) :
    1 / 6 * h ≤ (1 + ε) * (LD + LC) + (40 * η + B / 3) := by
  sorry
