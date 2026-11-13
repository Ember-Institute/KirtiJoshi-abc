/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatNoncriticalFunctions

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: actual positive ramification indices and the value/ramification
chain rule for all elementary rational composites and all algebraic points.
Sources: NoncriticalBasic.lean ramIdx_pos; NoncriticalElem.lean compK_spec.
The regular index uses minpoly over ℚ of the full residue-field element.
Values retain every embedding of that residue field into ℚbar. -/
theorem noncriticalCompositionRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    (∀ P : Place M.K, 0 < ramIdx M hDVR ψ P) ∧
    ∀ (hs : List NoncriticalP1.ElemMap) (x : QbarPoint M.K),
      Transcendental ℚ (NoncriticalP1.compK hs ψ) ∧
      noncriticalValue M x (NoncriticalP1.compK hs ψ) =
        NoncriticalP1.evalComp hs (noncriticalValue M x ψ) ∧
      ramIdx M hDVR (NoncriticalP1.compK hs ψ) x.P =
        ramIdx M hDVR ψ x.P *
          (NoncriticalP1.ramIdxComp hs (noncriticalValue M x ψ) : ℤ) := by
  sorry

end AbcAdaptation.Tripod.Fermat.Proper
