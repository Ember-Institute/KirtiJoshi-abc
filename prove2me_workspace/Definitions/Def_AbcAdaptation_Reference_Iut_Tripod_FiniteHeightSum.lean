/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight
import Solutions.Source_TripodFiniteHeightSupport

namespace AbcAdaptation.Reference.Iut.LocalHeightData

variable (L : LocalHeightData)

lemma deg_mul_height : (L.deg : ℝ) * L.height =
    ∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v) := by
  unfold height
  have h1 := L.one_le_deg
  have : (L.deg : ℝ) ≠ 0 := by exact_mod_cast (by omega : L.deg ≠ 0)
  field_simp

end AbcAdaptation.Reference.Iut.LocalHeightData

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut
open NumberField

variable (P : CurveProviders) (x : Pt)

/-- The provider height multiplied by the curve field degree is the finite height of `j`. -/
theorem finrank_mul_h_eq_finHeight :
    (Module.finrank ℚ (P.curve x).F : ℝ) * P.h x = finHeight (P.curve x).E.j := by
  classical
  have h := (P.localData x).deg_mul_height
  change ((P.localData x).deg : ℝ) * (P.localData x).height = _
  rw [h]
  have hmem : ∀ w, w ∈ (P.localData x).bad ↔ w ∈ (P.curve x).badAll := fun w =>
    (P.arith x).badAll_finite.mem_toFinset
  have hhv : ∀ w, (P.localData x).hv w =
      if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 := fun w => rfl
  have hf : ∀ w, (P.localData x).f w = inertDeg (P.curve x).F w := fun w => rfl
  have hp : ∀ w, (P.localData x).p w = residueChar w := fun w => rfl
  rw [finHeight_eq_sum (S := (P.localData x).bad) (fun w hw => ?_)]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [hmem] at hw
    rw [hhv, hf, hp, dif_pos hw, posLog_j_eq_of_mem_badAll P x hw]
  · refine (hmem w).mpr ?_
    by_contra h'
    exact hw (posLog_j_eq_zero_of_not_mem_badAll P x h')

end AbcAdaptation.Tripod
