/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (Cyclic.main_bound)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound
import Solutions.Source_TripodCyclicBoundOdd

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut WeierstrassCurve
open scoped Classical

theorem main_bound {P : CurveProviders} {x : Pt} {ℓ : ℕ} {hℓ : ℓ.Prime}
    {H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar))}
    {K : CompactlyBounded} (hx : x ∈ K.set) (hH : Nat.card H = ℓ) (hodd : ℓ ≠ 2)
    (hgal : ∀ σ : (P.curve x).Fbar ≃ₐ[(P.curve x).F] (P.curve x).Fbar, ∀ Q ∈ H,
      galPointMap (P.curve x).F (P.curve x).E (P.curve x).Fbar σ Q ∈ H)
    (hgraph : IsGraphLineOdd P x hℓ hodd H) {C₀ : ℝ} (hC₀1 : 1 ≤ C₀)
    (hC₀ : LegendreTorsionXBound K.c C₀) :
    ((ℓ : ℝ) - 1) / 4 * (P.h x - (P.localData x).heightEq 2) ≤
      10 * Real.log ℓ + (2 * Real.log (32 * C₀) + 6 * K.c + 4 * Real.log 4) := by
  sorry

end AbcAdaptation.Tripod.Cyclic
