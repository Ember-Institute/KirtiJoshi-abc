/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by the current reference adaptation:
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
Project adapter for the two bounds in Iut/Tripod/Height.lean:791.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeight
import Solutions.Source_TripodProviderAuxiliaryHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- The source provider theorem gives the existing fixed canonical comparison
for any supplied genuine source-shaped provider; provider existence is separate. -/
theorem canonicalLegendreHeightComparison_of_provider (P : CurveProviders) :
    CanonicalLegendreHeightComparison := by
  intro K
  obtain ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩ := legendreHeight P K
  refine ⟨max C₁ C₂, ?_⟩
  intro x hx
  have upper := h₁ x hx
  have lower := h₂ x hx
  simp only [Pi.smul_apply, smul_eq_mul, providerHeight_eq_auxiliaryHeight] at upper lower
  rw [abs_le]
  constructor
  · have hb := le_max_right C₁ C₂
    linarith
  · have hb := le_max_left C₁ C₂
    linarith

end AbcAdaptation.Tripod
