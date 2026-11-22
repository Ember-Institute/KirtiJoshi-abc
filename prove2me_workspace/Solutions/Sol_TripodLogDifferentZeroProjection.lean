/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/ClassicalAbc.lean
-/
import Definitions.Def_AbcTripod

set_option autoImplicit false

open AbcAdaptation.Tripod

theorem solution : LogDifferentZeroProjection := by
  intro q h0 h1
  have fieldEq : fieldOf (rationalPoint q h0 h1).1 = (⊥ : IntermediateField ℚ Qbar) :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨q, rfl⟩)
  let fieldEquiv : fieldOf (rationalPoint q h0 h1).1 ≃ₐ[ℚ] ℚ :=
    (IntermediateField.equivOfEq fieldEq).trans (IntermediateField.botEquiv ℚ Qbar)
  rw [logDiff, NumberField.discr_eq_discr_of_algEquiv _ fieldEquiv, Rat.numberField_discr]
  simp only [Int.cast_one, abs_one, Real.log_one, zero_div]
