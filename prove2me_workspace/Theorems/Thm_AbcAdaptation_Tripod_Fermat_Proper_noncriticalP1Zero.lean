/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatNoncriticalFunctions

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the actual P¹ noncritical theorem, at the rational point zero.
Source: NoncriticalP1/Main.lean exists_isNoncriticalBelyi, τ=some 0.
It constructs a list of actual rational Möbius maps and positive-degree
rational polynomials. No arbitrary function Pt→Pt or free law is supplied. -/
theorem noncriticalP1Zero (S : Finset NoncriticalP1.Pt)
    (hGal : ∀ σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar, ∀ z ∈ S, z.map σ ∈ S)
    (hZero : some 0 ∉ S) :
    ∃ hs : List NoncriticalP1.ElemMap,
      (∀ z ∈ S, NoncriticalP1.evalComp hs z ∈ NoncriticalP1.zeroOneInf) ∧
      NoncriticalP1.evalComp hs (some 0) ∉ NoncriticalP1.zeroOneInf ∧
      (∀ z, 1 < NoncriticalP1.ramIdxComp hs z →
        NoncriticalP1.evalComp hs z ∈ NoncriticalP1.zeroOneInf) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
