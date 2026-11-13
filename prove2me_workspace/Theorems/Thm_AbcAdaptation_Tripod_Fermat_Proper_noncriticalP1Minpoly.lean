/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/NoncriticalP1/Reduction.lean minpoly_step.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 097aace5620aa31d0eb75b0f976cffff02d655ebcd3c15fd6cee9726f101bc53.
-/
import Definitions.Def_FermatNoncriticalP1Reduction

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

open NoncriticalP1

/-- OPEN: exact source `minpoly_step` statement, with project namespace and
transparent concrete conjunction in place of source structure. -/
theorem noncriticalP1Minpoly (T : Finset Tripod.Qbar) (hT : IsGalStable T) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    {d n : ℕ} (hd : 2 ≤ d) (hdeg : ∀ y ∈ T, deg y ≤ d)
    (hcard : (T.filter fun y => deg y = d).card ≤ n + 1) {σ₀ : Tripod.Qbar} (hσ₀ : σ₀ ∈ T)
    (hσ₀d : deg σ₀ = d) :
    ∃ (T₂ : Finset Tripod.Qbar) (τ₂ : ℚ), IsGalStable T₂ ∧ (τ₂ : Tripod.Qbar) ∉ T₂ ∧
      (∀ y ∈ T₂, deg y ≤ d) ∧ (T₂.filter fun y => deg y = d).card ≤ n ∧
      ∃ u : ElemMap, ∀ hs, IsNoncriticalBelyi hs (withInf T₂) (ofRat τ₂) →
        IsNoncriticalBelyi (u :: hs) (withInf T) (ofRat 9) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
