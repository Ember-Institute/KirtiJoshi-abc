/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of the high-height composition in
Iut/Implication/Corollary23.lean. The mathematical children are explicit
hypotheses; this file does not import their open theorem declarations.
-/
import Definitions.Def_TripodCanonicalHighHeightInputs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- The exact canonical children imply the existing `HighHeightEstimate`.
The finite exceptional set is absorbed into the final `htCan` threshold.
The error coefficient is enlarged with existing `logDiff_nonneg` and
`logCond_nonneg`; no Northcott input is needed for this high-height step. -/
theorem highHeightEstimate_of_canonical_children
    (hCompare : CanonicalLegendreHeightComparison)
    (hC2 : CanonicalCorollary22HighHeightEstimate)
    (hEpsilon : EpsilonELargeHeight) : HighHeightEstimate := by
  intro d hd ε hε K
  obtain ⟨B, hB⟩ := hCompare K
  obtain ⟨E, H₂, C₂, hE, hc2⟩ := hC2 d hd K
  obtain ⟨M, hM⟩ := (hE.image (fun x : Pt => htCan x)).bddAbove
  let T : ℝ := max H₂
    (max (((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4) / ε) ^ 4) 1)
  refine ⟨max M (T / 6 + B), C₂ + B, ?_⟩
  intro x hxK hxd hxH
  have hCompareX := (abs_le.mp (hB x hxK)).1
  have hTransfer : htCan x ≤ auxiliaryHeight x / 6 + B := by
    linarith
  have hxE : x ∉ E := by
    intro hxE
    have hxM : htCan x ≤ M := hM (Set.mem_image_of_mem _ hxE)
    have hMH : M ≤ max M (T / 6 + B) := le_max_left _ _
    linarith
  have hT : T ≤ auxiliaryHeight x := by
    have hTH : T / 6 + B ≤ max M (T / 6 + B) := le_max_right _ _
    linarith
  have hH₂ : H₂ ≤ auxiliaryHeight x := (le_max_left _ _).trans hT
  have hδ : 1 ≤ deltaBound d := by
    have hdNat : 1 ≤ d := hd
    have hdReal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdNat
    unfold deltaBound
    linarith
  have hεE : epsilonE (deltaBound d) (auxiliaryHeight x) ≤ ε := by
    apply hEpsilon (deltaBound d) (auxiliaryHeight x) ε hδ hε
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    · exact ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  obtain ⟨hEstimate, _, _⟩ := hc2 x hxK hxd hxE hH₂
  have hNonneg : 0 ≤ logDiff x + logCond x :=
    add_nonneg (logDiff_nonneg x) (logCond_nonneg x)
  have hCoefficient :
      (1 + epsilonE (deltaBound d) (auxiliaryHeight x)) *
          (logDiff x + logCond x) ≤
        (1 + ε) * (logDiff x + logCond x) :=
    mul_le_mul_of_nonneg_right (add_le_add le_rfl hεE) hNonneg
  linarith

end AbcAdaptation.Tripod
