/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
/- Adapted from lana-agents/belyi, commit 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8; complete source signature selected by the original Lean parser. -/
import Definitions.Def_FermatNoncriticalP1Reduction

set_option autoImplicit false
open scoped Classical
namespace AbcAdaptation.Tripod.Fermat.Proper
open NoncriticalP1
open Polynomial IntermediateField

theorem noncriticalP1RationalBranchSet (T : Finset ℚ) (τ : ℚ) (hT : ∀ t ∈ T, |t| ≤ 1)
    (hτ : 9 ≤ τ) :
    ∃ hs : List ElemMap, IsNoncriticalBelyi hs (insert none (ofRat '' (T : Set ℚ))) (ofRat τ) := by sorry

end AbcAdaptation.Tripod.Fermat.Proper
