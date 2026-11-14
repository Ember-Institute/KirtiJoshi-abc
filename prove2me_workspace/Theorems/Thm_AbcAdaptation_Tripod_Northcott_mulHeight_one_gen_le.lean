/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Modified adaptation, 2026-11-14: exact concrete Northcott proof from
refer/iut/Iut/Tripod/Northcott.lean. Uses the existing independent tripod
carrier and Mathlib only. Source hashes and revision status: SOURCE_MANIFEST.json.
-/
import Definitions.Def_TripodNorthcottInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Northcott

open NumberField Polynomial

/-- The multiplicative height `exp (logHeight₁ (gen λ))` of a point of degree `≤ d` and height
`htCan ≤ H` is at most `heightBound d H = exp (d · max H 0)`. -/
theorem mulHeight_one_gen_le {d : ℕ} {H : ℝ} {x : Pt} (hd : x ∈ ptLE d) (hH : htCan x ≤ H) :
    Height.mulHeight₁ (gen x.1) ≤ heightBound d H := by
  rw [heightBound, ← Real.exp_log (Height.mulHeight₁_pos _),
    ← Height.logHeight₁_eq_log_mulHeight₁]
  apply Real.exp_le_exp.mpr
  rw [← deg_mul_htCan x]
  exact mul_le_mul (by exact_mod_cast hd) (hH.trans (le_max_left _ _)) (htCan_nonneg _)
    (Nat.cast_nonneg _)

end AbcAdaptation.Tripod.Northcott
