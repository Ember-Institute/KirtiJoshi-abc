/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ThetaLocalConstruct/Ordp.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder
import Solutions.Source_ReferenceIutConcreteLocalArithmetic
import Solutions.Source_ReferenceIutEmbedCompletion
import Solutions.Source_TripodRelativeDegreeTower
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField TateCurvesTheta WithZero
open scoped WithZero

/-- Normalized order is invariant under the comparison map of completions. -/
theorem ordp_embedCompletion {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] {v : FinitePlace K} {w : FinitePlace k}
    (hvw : FinitePlace.LiesOver v w) (y : localCompletion w) :
    ordp K v (embedCompletion hvw y) = ordp k w y := by
  by_cases hy : y = 0
  · subst y
    simp [ordp]
  have hyv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  let m : ℤ := log (Valued.v y)
  have hm : Valued.v y = exp m := (exp_log hyv).symm
  have hmv : Valued.v (embedCompletion hvw y) = exp ((Tripod.relRamIdx v w : ℤ) * m) := by
    rw [valued_embedCompletion, hm, ← exp_nsmul, nsmul_eq_mul]
  have hram : ramIdx K v = ramIdx k w * Tripod.relRamIdx v w := Tripod.ramIdx_eq_mul hvw
  have he : (Tripod.relRamIdx v w : ℝ) ≠ 0 := by exact_mod_cast Tripod.relRamIdx_ne_zero hvw
  have hw : (ramIdx k w : ℝ) ≠ 0 := by exact_mod_cast (LocalConstruct.ramIdx_pos w).ne'
  rw [LocalConstruct.ordp_eq_of_valued v _ _ hmv, LocalConstruct.ordp_eq_of_valued w y m hm, hram]
  push_cast
  field_simp [he, hw] <;> ring

/-- The normalized order of the Tate parameter is its integer order divided by `e_w`. -/
theorem ordp_tateParameter {k : Type*} [Field k] [NumberField k] {w : FinitePlace k}
    (t : TateParameter (localCompletion w)) {π : localCompletion w} (hπ : IsUniformizer π) :
    ordp k w (t.q : localCompletion w) = ((t.toOrdered hπ).orderNat : ℝ) / ramIdx k w := by
  rw [LocalConstruct.ordp_eq_of_valued w _ _ (valued_tateParameter_q t hπ),
    Int.cast_neg, Int.cast_natCast, neg_neg]

end AbcAdaptation.Reference.Iut
