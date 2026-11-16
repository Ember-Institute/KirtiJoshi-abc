/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Open Act1 statement adapted from Iut/Implication/Theorem110.lean at commit
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8. Original proof bytes are preserved in
source/OriginalCommand.lean. This file deliberately contains an open proof. -/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.Theorem110Invariants
universe u v

theorem AbcAdaptation.Reference.Iut.Theorem110Invariants.theorem110
    {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {X : Corollary312VariantData.{u, v} AG TG}
    (inv : Theorem110Invariants X)
    (cert : Theorem110Certificate inv) (est : inv.LocalEstimate)
    (pnt : PrimeCountingBound) (h312 : Corollary312Variant X) :
    1 / 6 * X.qPilot.logQ ≤
      (1 + 20 * (X.dmod : ℝ) / X.ℓ) * (inv.logDtpd + inv.logFtpd) +
        20 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) := by
  sorry
