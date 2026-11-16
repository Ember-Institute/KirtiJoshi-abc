/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Exact source proof candidate. Source: Iut/Implication/Invariants.lean#L166-L167.
No source compilation or target acceptance is claimed. -/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.Theorem110Invariants
universe u v

theorem AbcAdaptation.Reference.Iut.Theorem110Invariants.iota_nonneg {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {X : Corollary312VariantData.{u, v} AG TG}
    (inv : Theorem110Invariants X) (p : ℕ) :
    0 ≤ inv.ι p := by
  unfold ι; split_ifs <;> norm_num
