/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean (sl2Image)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Theorems.Thm_AbcAdaptation_Reference_Iut_EllipticCurveData_sl_le_range_of

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut

theorem solution (P : CurveProviders) : SL2ImageHyp P := by
  classical
  intro x ℓ hℓ h5 hP2 hP4 hP5 A
  have hP2' : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw := by
    intro w hw
    have := hP2 w ((P.arith x).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0) at this
    rwa [dif_pos hw] at this
  have hP5' : ∃ w ∈ (P.curve x).badAll,
      AbcAdaptation.Reference.Iut.residueChar w ≠ 2 ∧
      AbcAdaptation.Reference.Iut.residueChar w ≠ ℓ := by
    obtain ⟨w, hw, h⟩ := hP5
    exact ⟨w, (P.arith x).badAll_finite.mem_toFinset.mp hw, h⟩
  exact (P.curve x).sl_le_range_of (P.arith x) (P.tate x) hℓ (P.modRep x ℓ hℓ) h5 hP2' hP4 hP5' A
