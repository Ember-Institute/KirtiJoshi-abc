/-
Adaptation provenance: original source Iut/Implication/Theorem110.lean.
Original authors: The iut contributors.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original license: Apache-2.0; the original notice is retained below.
Namespace and Mathlib import paths are adapted to this independent project.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
namespace AbcAdaptation.Reference
namespace Iut
/-- The sum of an affine-quadratic expression over `Fin L`, via (E1) and (E2):
`∑_{i<L} (a(i+2) + b(i+1)² + c) = a·L(L+3)/2 + b·L(L+1)(2L+1)/6 + c·L`. -/
lemma sum_affine_quadratic (L : ℕ) (a b c : ℝ) :
    ∑ i : Fin L, (a * ((i : ℝ) + 2) + b * ((i : ℝ) + 1) ^ 2 + c) =
      a * (L * (L + 3) / 2) + b * (L * (L + 1) * (2 * L + 1) / 6) + c * L := by
  rw [Fin.sum_univ_eq_sum_range (fun i => a * ((i : ℝ) + 2) + b * ((i : ℝ) + 1) ^ 2 + c) L]
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
end Iut
end AbcAdaptation.Reference
