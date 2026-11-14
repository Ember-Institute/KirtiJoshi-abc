/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of Iut/Tripod/Height.lean and TwoAdic.lean.
Archived source hashes are recorded in this unit's source-consumer.json.
Historical upstream revision is unverified. No Iut or Genl module is imported.
-/
/- Complete source proof body: Iut/Tripod/Height.lean:490-504.
Uncompiled adaptation, specialized to the fixed actual generator. -/
import Definitions.Def_TripodLegendreHeightBasics
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod

theorem legendreZeroJRootOfUnity : LegendreZeroJRootOfUnity := by
  intro x hj
  have hl0 := gen_ne_zero x.2.1
  have hl1 := gen_ne_one x
  have h256 : (256 : fieldOf x.1) ≠ 0 := by
    have : (256 : fieldOf x.1) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hden : gen x.1 ^ 2 * (gen x.1 - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  rw [legendreJ, div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff (by norm_num)] at hj
  rcases hj with (h | h) | h
  · exact absurd h h256
  · have h3 : gen x.1 ^ 3 = -1 := by linear_combination (gen x.1 + 1) * h
    calc gen x.1 ^ 6 = (gen x.1 ^ 3) ^ 2 := by ring
         _ = 1 := by rw [h3]; ring
  · exact absurd h hden

end AbcAdaptation.Tripod
