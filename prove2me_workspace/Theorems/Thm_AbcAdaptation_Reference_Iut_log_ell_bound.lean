/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Namespace adaptation of the complete original source command. The proof body
and signature bytes are retained. Validation is recorded in the delivery evidence. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_self_of_pos

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference
namespace Iut
universe u v w
open Finset Real

/-- The bound on `log ℓ` from (P1): `log ℓ ≤ 3 + 2δ + 8·√√h` when `ℓ ≤ 20δ²h²`. -/
lemma log_ell_bound {δ h ℓ s : ℝ} (hδ : 1 ≤ δ) (hh1 : 1 ≤ h) (hℓ : 1 ≤ ℓ)
    (hℓup : ℓ ≤ 20 * δ ^ 2 * h ^ 2) (hlogh : Real.log h ≤ 4 * s) :
    Real.log ℓ ≤ 3 + 2 * δ + 8 * s := by
  have h1 : Real.log ℓ ≤ Real.log (20 * δ ^ 2 * h ^ 2) := Real.log_le_log (by linarith) hℓup
  have h2 : Real.log (20 * δ ^ 2 * h ^ 2) = Real.log 20 + 2 * Real.log δ + 2 * Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have h3 : Real.log 20 ≤ 3 := by
    have : Real.log 20 ≤ Real.log (Real.exp 3) :=
      Real.log_le_log (by norm_num) (by
        have := Real.exp_one_gt_d9
        have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have h4 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
          pow_le_pow_left₀ (by norm_num) this.le 3
        rw [h3]; norm_num at h4 ⊢; linarith)
    rwa [Real.log_exp] at this
  have h4 : Real.log δ ≤ δ := log_le_self_of_pos (by linarith)
  linarith

end Iut
end AbcAdaptation.Reference
