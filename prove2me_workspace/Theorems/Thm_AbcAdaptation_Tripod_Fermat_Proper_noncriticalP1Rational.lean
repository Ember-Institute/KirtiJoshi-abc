/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/NoncriticalP1/Reduction.lean rational_step.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 097aace5620aa31d0eb75b0f976cffff02d655ebcd3c15fd6cee9726f101bc53.
-/
import Definitions.Def_FermatNoncriticalP1Reduction

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

open NoncriticalP1

/-- OPEN: exact source `rational_step` statement, with project namespace and
transparent concrete conjunction in place of source structure. -/
theorem noncriticalP1Rational (T : Finset Tripod.Qbar) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    (hdeg : ∀ y ∈ T, deg y ≤ 1) :
    ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat 9) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
