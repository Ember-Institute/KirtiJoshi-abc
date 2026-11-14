/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of Iut/Tripod/Height.lean and TwoAdic.lean.
Archived source hashes are recorded in this unit's source-consumer.json.
Historical upstream revision is unverified. No Iut or Genl module is imported.
-/
/- Source proof bodies: Iut/Tripod/Height.lean:62-81,509-529;
Iut/Tripod/TwoAdic.lean:470. Uncompiled independent draft. -/
import Definitions.Def_TripodLegendreHeightComparisonInputs
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open NumberField

namespace AbcAdaptation.Tripod

noncomputable def infHeight {T : Type*} [Field T] [NumberField T] (y : T) : ℝ :=
  ∑ w : InfinitePlace T, (w.mult : ℝ) * Real.posLog (w y)

theorem logHeight₁_eq_infHeight_add_finHeight {T : Type*} [Field T] [NumberField T]
    (y : T) : Height.logHeight₁ y = infHeight y + finHeight y :=
  logHeight₁_eq y

theorem infHeight_nonneg {T : Type*} [Field T] [NumberField T] (y : T) :
    0 ≤ infHeight y :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg

theorem finHeight_le_logHeight₁ {T : Type*} [Field T] [NumberField T] (y : T) :
    finHeight y ≤ Height.logHeight₁ y := by
  rw [logHeight₁_eq_infHeight_add_finHeight]
  linarith [infHeight_nonneg y]

@[simp] theorem finHeight_zero {T : Type*} [Field T] [NumberField T] :
    finHeight (0 : T) = 0 := by simp [finHeight]

theorem infHeight_le_of_forall {T : Type*} [Field T] [NumberField T] {y : T} {c : ℝ}
    (h : ∀ w : InfinitePlace T, Real.posLog (w y) ≤ c) :
    infHeight y ≤ c * Module.finrank ℚ T := by
  unfold infHeight
  calc ∑ w : InfinitePlace T, (w.mult : ℝ) * Real.posLog (w y)
      ≤ ∑ w : InfinitePlace T, (w.mult : ℝ) * c :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (Nat.cast_nonneg _)
    _ = c * Module.finrank ℚ T := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, mul_comm]

theorem posLog_le_abs_log (t : ℝ) : Real.posLog t ≤ |Real.log t| := by
  rw [Real.posLog_apply]
  exact max_le (abs_nonneg _) (le_abs_self _)

theorem posLog_inv_le_abs_log (t : ℝ) : Real.posLog t⁻¹ ≤ |Real.log t| := by
  rw [Real.posLog_apply, Real.log_inv]
  exact max_le (abs_nonneg _) (neg_le_abs _)

theorem CompactlyBounded.c_nonneg {K : CompactlyBounded} {x : Pt}
    (hx : x ∈ K.set) : 0 ≤ K.c := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace (fieldOf x.1)) := inferInstance
  exact (abs_nonneg _).trans (hx.2 w).1

theorem gen_ne_one (x : Pt) : gen x.1 ≠ 1 :=
  sub_ne_zero.mp (gen_sub_one_ne_zero x.2.2)

end AbcAdaptation.Tripod
