/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean (curveInputs)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeight
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp
import Solutions.Source_TripodCurveInputsDmodField
import Solutions.Source_TripodCurveInputsFieldArithmetic

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference AbcAdaptation.Reference.Iut

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- Assemble the curve data with the explicit image lemma used in the source constructor. -/
noncomputable def curveInputsOfSL2Image {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG) (hN : NorthcottHyp)
    (hdeg3 : ∀ x : Pt, TorsionDegreeBound x.1 3) (hdeg5 : ∀ x : Pt, TorsionDegreeBound x.1 5)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (hge : LogCondGeHyp P) (hle : LogCondLeHyp P) (hSL2 : SL2ImageHyp P) :
    CurveInputs tripodTheory AG K d where
  h := P.h
  curve x _ := P.curve x
  arith x _ := P.arith x
  tate x _ := P.tate x
  modRep x _ ℓ hℓ := P.modRep x ℓ hℓ
  height_eq _ _ := rfl
  deg_le := curveInputs_deg_le P K d hdeg3 hdeg5
  dmod_le := curveInputs_dmod_le P K d
  htCan_equiv := hh
  northcott := northcott_of_equiv hN K d hh
  B := max (4 * K.c) 0
  B_nonneg := le_max_right _ _
  heightEq_two_le x hx := hB x hx.1
  HasCyclicSubgroup x ℓ := (P.curve x).HasCyclicSubgroup ℓ
  TK := TK
  cyclic_bound := CF.cyclic
  sl2_of x _ ℓ hℓ := hSL2 x ℓ hℓ
  logDiff_eq := curveInputs_logDiff_eq P K d
  excCore_finite := hcore
  logCond_ge x _ := hge x
  logCond_le x _ := hle x

end AbcAdaptation.Tripod
