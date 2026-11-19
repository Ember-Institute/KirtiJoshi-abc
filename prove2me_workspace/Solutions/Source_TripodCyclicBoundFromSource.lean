/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (cyclicBoundOdd)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound
import Solutions.Source_ReferenceHeightsTorsionBound
import Solutions.Source_TripodCyclicLocal

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- The reference cyclic bound at the torsion constant chosen from the archimedean theorem. -/
theorem cyclicBoundOdd_of_source (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (harch : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ LegendreTorsionXBound K.c C₀)
    (hlocal : CyclicLocalGraphLineHyp P)
    (hmain : ∀ {C₀ : ℝ}, 1 ≤ C₀ → LegendreTorsionXBound K.c C₀ → CyclicMainBoundHyp P K C₀) :
    CyclicBoundOddHyp P K d (cyclicConst K (torsionConst K.c harch)) :=
  cyclicBoundOdd_of_isogeny P K d hlocal
    (hmain (one_le_torsionConst K.c harch) (torsionConst_spec K.c harch))

/-- The cyclic bound at the Legendre torsion constant, given the Vélu estimate. -/
theorem cyclicBoundOdd_of_mainBound (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (hmain : ∀ {C₀ : ℝ}, 1 ≤ C₀ → LegendreTorsionXBound K.c C₀ → CyclicMainBoundHyp P K C₀) :
    CyclicBoundOddHyp P K d
      (cyclicConst K (torsionConst K.c (legendre_torsion_x_le_from_source K.c))) :=
  cyclicBoundOdd_of_source P K d (legendre_torsion_x_le_from_source K.c)
    (cyclicLocalGraphLine_from_source P) hmain

end AbcAdaptation.Tripod
