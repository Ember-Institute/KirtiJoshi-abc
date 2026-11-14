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

universe u v

































end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.assembly {ℓ d D Q S T P DF E e lg : ℝ} (hℓ : 7 ≤ ℓ) (hd : 1 ≤ d) (_hD : 0 ≤ D)
    (_hQ : 0 ≤ Q) (_hS : 0 ≤ S) (_hT : 0 ≤ T) (_hP0 : 0 ≤ P) (hP : P ≤ 2) (hDF : 0 ≤ DF)
    (_hlg0 : 0 ≤ lg) (hlg : lg ≤ ℓ) (he : 552960 * ℓ ≤ e) (hE : e ≤ E)
    (h1 : -12 * Q ≤ 6 * ℓ * (ℓ + 5) * D - ℓ * (ℓ + 1) * Q + 24 * ℓ * S +
      24 * ℓ * (ℓ + 5) * T + 6 * ℓ * (ℓ + 5) * P)
    (h2 : D ≤ DF + 2 * lg + 21) (h3 : S ≤ 2 * d * DF + 5 + lg) (h4 : 2 * T ≤ 3 * E) :
    ℓ * Q ≤ 6 * (ℓ + 20 * d) * DF + 120 * ℓ * E := by
  sorry
