/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AbcAdaptation.Reference
open AbcAdaptation.Reference.Iut
universe u v w

theorem AbcAdaptation.Reference.Iut.Corollary22Inputs.c2
    {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d)
    {P : Corollary312VariantData.{u, v} AG TG → Prop} (hd : 1 ≤ d)
    (ex : ThetaDataExistence P I) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, P X → Corollary312Variant X)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d) (hxe : x ∉ I.excCore)
    (hH : I.threshold cheb ≤ I.h x) :
    1 / 6 * I.h x ≤ (1 + epsilonE (deltaBound d) (I.h x)) *
        (T.logDiff T.tripod x + T.logCond T.tripod x) + (40 * pnt.η + I.B / 3) ∧
      epsilonE (deltaBound d) (I.h x) ≤ 1 ∧
      0 ≤ T.logDiff T.tripod x + T.logCond T.tripod x := by
  sorry
