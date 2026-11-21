/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors

Original repository https://github.com/lana-agents/tate-curves-theta
Original revision ca6c2279d3cea0690cdb01328e727118d5485d68
Original paths TateCurvesTheta/TateCurve/TateUniformization.lean,
TateCurvesTheta/TateCurve/PointMap.lean and TateCurvesTheta/TateCurve/GroupLaw.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure

set_option autoImplicit false

open AbcAdaptation.Reference.TateCurvesTheta WeierstrassCurve
open scoped Classical

/-- The quotient uniformization of a Tate curve has the Tate series as its coordinates. -/
theorem AbcAdaptation.Reference.Iut.exists_tateUniformization
    {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (t : TateParameter k) (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) :
    ∃ iso : Additive (kˣ ⧸ Subgroup.zpowers t.q) ≃+ t.tateCurve.toAffine.Point,
      (∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) →
        (match iso (Additive.ofMul (QuotientGroup.mk u)) with
          | .zero => 0
          | .some x _ _ => x) = t.X u) ∧
      (∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) →
        (match iso (Additive.ofMul (QuotientGroup.mk u)) with
          | .zero => 0
          | .some _ y _ => y) = t.Y u) := by
  sorry
