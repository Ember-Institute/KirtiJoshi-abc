/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Namespace adaptation of the complete original source command. The proof body
and signature bytes are retained. The private platform accepted this proof;
the named theorem is retained here for its downstream consumers. -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference
namespace Iut
universe u v w
open Finset Real

/-- The (P5) argument: if `h ≤ B + √h·log ℓ` with `log ℓ ≤ 3 + 2δ + 8·√√h`, then
`h ≤ (B + 11 + 2δ)⁴`. -/
lemma p5_height_bound {B δ h r s lg : ℝ} (hB : 0 ≤ B) (hδ : 1 ≤ δ) (_hr0 : 0 ≤ r)
    (hrr : r * r = h) (hs0 : 0 ≤ s) (hss : s * s = r) (hh1 : 1 ≤ h)
    (hlg : lg ≤ 3 + 2 * δ + 8 * s) (hmain : h ≤ B + r * lg) :
    h ≤ (B + 11 + 2 * δ) ^ 4 := by
  have hs4 : s * s * (s * s) = h := by rw [hss]; exact hrr
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  have hrs : r * lg ≤ (3 + 2 * δ) * (s * s) + 8 * (s * s * s) := by
    rw [← hss]; nlinarith [mul_le_mul_of_nonneg_left hlg (by positivity : (0:ℝ) ≤ s * s)]
  have hs3 : s * s * (s * s) ≤ B + (11 + 2 * δ) * (s * s * s) := by
    have : (3 + 2 * δ) * (s * s) ≤ (3 + 2 * δ) * (s * s * s) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    nlinarith
  have hsle : s ≤ B + 11 + 2 * δ := by
    have hs3' : 0 < s * s * s := by positivity
    have : (s * s * s) * s ≤ (s * s * s) * (B + 11 + 2 * δ) := by
      have : B ≤ B * (s * s * s) := le_mul_of_one_le_right hB (by nlinarith)
      nlinarith
    exact le_of_mul_le_mul_left this hs3'
  rw [← hs4]
  calc s * s * (s * s) = s ^ 4 := by ring
    _ ≤ (B + 11 + 2 * δ) ^ 4 := pow_le_pow_left₀ hs0 hsle 4

end Iut
end AbcAdaptation.Reference
