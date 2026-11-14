/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of Iut/Tripod/Height.lean and TwoAdic.lean.
Archived source hashes are recorded in this unit's source-consumer.json.
Historical upstream revision is unverified. No Iut or Genl module is imported.
-/
/- Complete source proof body: Iut/Tripod/Height.lean:632-669.
Uncompiled adaptation; no provider or elliptic-curve assumptions. -/
import Definitions.Def_TripodLegendreHeightBasics

set_option autoImplicit false
open NumberField

namespace AbcAdaptation.Tripod

theorem legendreArchimedeanTripleBound : LegendreArchimedeanTripleBound := by
  intro K x hx
  have hplace : ∀ w : InfinitePlace (fieldOf x.1),
      Real.posLog (w (gen x.1)) ≤ K.c ∧ Real.posLog (w (gen x.1)⁻¹) ≤ K.c ∧
      Real.posLog (w (gen x.1 - 1)⁻¹) ≤ K.c := by
    intro w
    obtain ⟨h1, h2⟩ := hx.2 w
    refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
    · rw [map_inv₀]
      exact (posLog_inv_le_abs_log _).trans h1
    · rw [map_inv₀]
      exact (posLog_inv_le_abs_log _).trans h2
  have key : ∀ y : fieldOf x.1,
      (∀ w : InfinitePlace (fieldOf x.1), Real.posLog (w y) ≤ K.c) →
      Height.logHeight₁ y ≤ finHeight y + K.c * deg x.1 := by
    intro y hy
    rw [logHeight₁_eq_infHeight_add_finHeight, deg_eq_finrank]
    linarith [infHeight_le_of_forall hy]
  exact ⟨key _ fun w => (hplace w).1, key _ fun w => (hplace w).2.1,
    key _ fun w => (hplace w).2.2⟩

end AbcAdaptation.Tripod
