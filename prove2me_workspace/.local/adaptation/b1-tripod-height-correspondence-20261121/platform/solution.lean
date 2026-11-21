/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
import Definitions.Def_TripodCanonicalHighHeightInputs
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Theorems.Thm_AbcAdaptation_Tripod_finrank_mul_h_eq_finHeight
import Theorems.Thm_AbcAdaptation_Tripod_finHeight_mapEquiv
import Theorems.Thm_AbcAdaptation_Tripod_finHeight_algebraMap
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut NumberField

theorem solution (P : CurveProviders) (x : Pt) : P.h x = finHeight (legendreJ (gen x.1)) / deg x.1 := by
  have h1 := finrank_mul_h_eq_finHeight P x
  haveI : Module.Finite (tpd P x) (P.curve x).F := Module.Finite.right ℚ (tpd P x) (P.curve x).F
  have hT : finHeight (jT P x) = finHeight (legendreJ (gen x.1)) := by
    rw [← tpdEquiv_jT]
    exact (finHeight_mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) (jT P x)).symm
  rw [curve_j_eq_algebraMap, finHeight_algebraMap, hT] at h1
  have h2 : (Module.finrank ℚ (P.curve x).F : ℝ) =
      deg x.1 * Module.finrank (tpd P x) (P.curve x).F := by
    rw [← finrank_tpd P x]
    exact_mod_cast (Module.finrank_mul_finrank ℚ (tpd P x) (P.curve x).F).symm
  have h3 : (Module.finrank (tpd P x) (P.curve x).F : ℝ) ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < Module.finrank ℚ (P.curve x).F := by
      exact_mod_cast Module.finrank_pos
    rw [h2, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [h2] at h1
  rw [eq_div_iff (deg_pos_real x.1).ne']
  apply mul_left_cancel₀ h3
  calc (Module.finrank (tpd P x) (P.curve x).F : ℝ) * (P.h x * deg x.1)
      = deg x.1 * Module.finrank (tpd P x) (P.curve x).F * P.h x := by ring
    _ = _ := h1
