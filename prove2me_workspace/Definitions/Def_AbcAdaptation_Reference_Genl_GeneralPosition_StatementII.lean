/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Definitions.Def_AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory
import Definitions.Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy
import Mathlib.Algebra.Group.Action.Pi

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
namespace AbcAdaptation.Reference.Genl.HeightTheory
variable (T : HeightTheory)

/-- Statement (ii) of Theorem 2.1 of [mochizuki2010]: the ABC conjecture for
`Σ`-supported compactly bounded subsets. For every compactly bounded subset
`K_V ⊆ U_ℙ(ℚ̄)` whose support contains `Σ`, every positive integer `d` and every `ε > 0`,
the inequality of BD-classes

`ht_{ω_ℙ(C)} ≲ (1 + ε) (log-diff_ℙ + log-cond_C)`

holds on `K_V ∩ U_ℙ(ℚ̄)^{≤d}`, where `C = {0, 1, ∞} ⊆ ℙ = ℙ¹_ℚ`. -/
def StatementII : Prop :=
  ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ K : T.CBS,
    T.htCan T.tripod ≲[T.cbsSet K ∩ T.ptLE T.tripod d]
      (1 + ε) • (T.logDiff T.tripod + T.logCond T.tripod)

end AbcAdaptation.Reference.Genl.HeightTheory
