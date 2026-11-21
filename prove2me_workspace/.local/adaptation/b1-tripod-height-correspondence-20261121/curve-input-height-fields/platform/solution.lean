/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Sources at revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Iut/Tripod/CurveFacts.lean:498-509
Iut/Concrete/Existence.lean:402-410,474-480
Iut/Tripod/Basic.lean:451-465
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp
import Theorems.Thm_AbcAdaptation_Tripod_legendreHeight
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference

theorem solution (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    (∀ x : Pt, x ∈ K.set ∩ ptLE d →
      ((P.curve x).localHeightData (P.arith x) (P.tate x)).height = P.h x) ∧
    LegendreHeightHyp P K ∧
    (∀ H : ℝ, {x : Pt | x ∈ K.set ∩ ptLE d ∧ P.h x ≤ H}.Finite) := by
  have hh : ((1 / 6 : ℝ) • P.h) ≈[K.set] htCan := legendreHeight P K
  refine ⟨fun _ _ => rfl, hh, ?_⟩
  intro H
  obtain ⟨C, hC⟩ := hh.2
  refine (boundedDegreeFiniteness d (H / 6 + C)).subset fun x hx ↦ ⟨hx.1.2, ?_⟩
  have hcan := hC x hx.1.1
  simp only [Pi.smul_apply, smul_eq_mul] at hcan
  linarith [hx.2]
