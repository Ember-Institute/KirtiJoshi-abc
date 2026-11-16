/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators
open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.Theorem110Invariants
universe u v

theorem AbcAdaptation.Reference.Iut.Theorem110Invariants.LocalEstimate.rhs_le
    {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {X : Corollary312VariantData.{u, v} AG TG} {inv : Theorem110Invariants X}
    (est : inv.LocalEstimate) :
    X.rhsData.rhs ≤
      (∑ i, (∑ p ∈ inv.dst, inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
        (X.rhsData.container.proc.capsule i).card * Real.log Real.pi)) /
        X.rhsData.container.proc.length := by
  sorry
