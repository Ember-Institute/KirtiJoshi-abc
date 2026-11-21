/-
Adapted from TateCurvesTheta/TateCurve/PointMap.lean at
ca6c2279d3cea0690cdb01328e727118d5485d68 in lana-agents/tate-curves-theta.
-/
/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Parametrization
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

open WeierstrassCurve
open scoped Classical

noncomputable section

namespace TateCurvesTheta.TateParameter

variable {k : Type*} [NormedField k] (t : TateParameter k)

lemma mem_zpowers_q_iff (u : kˣ) :
    u ∈ Subgroup.zpowers t.q ↔ ∃ n : ℤ, (t.q : k) ^ n * (u : k) = 1 := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have hu : (u : k) = (t.q : k) ^ n := by rw [← hn, Units.val_zpow_eq_zpow_val]
    rw [hu, ← zpow_add₀ t.q.ne_zero, neg_add_cancel, zpow_zero]
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one]
    exact hn

/-- The Weierstrass equation for the Tate coordinate series away from the powers of the parameter. -/
def TatePointEquation : Prop :=
  ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)

variable [CompleteSpace k] [IsUltrametricDist k]
variable (hmem : t.TatePointEquation) (h12 : (12 : k) ≠ 0)

/-- The Tate point at a unit is the point at infinity on the powers of the parameter.
Its affine coordinates elsewhere are the Tate series. -/
def tatePoint (u : kˣ) : t.tateCurve.toAffine.Point :=
  if hu : u ∈ Subgroup.zpowers t.q then 0
  else
    .some (t.X u) (t.Y u) <|
      (t.tateCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (t.tateCurve_Δ_ne_zero h12)).mp <|
        hmem u fun n hn => hu ((t.mem_zpowers_q_iff u).mpr ⟨n, hn⟩)

lemma tatePoint_eq_zero_iff (u : kˣ) :
    t.tatePoint hmem h12 u = 0 ↔ u ∈ Subgroup.zpowers t.q := by
  by_cases hu : u ∈ Subgroup.zpowers t.q
  · simp [tatePoint, hu]
  · rw [tatePoint, dif_neg hu]
    exact ⟨fun h => (Affine.Point.some_ne_zero _ h).elim, fun h => (hu h).elim⟩

end TateCurvesTheta.TateParameter

end

end AbcAdaptation.Reference
