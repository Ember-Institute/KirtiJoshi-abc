/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicArch.lean and Iut/Tripod/CyclicIsogeny.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical

/-- The uniform bound on affine torsion coordinates of complex Legendre curves. -/
def LegendreTorsionXBound (c C₀ : ℝ) : Prop :=
  ∀ (l : ℂ), |Real.log ‖l‖| ≤ c → |Real.log ‖l - 1‖| ≤ c →
    ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
      ∀ {N : ℕ}, 1 ≤ N → ∀ {a b : ℂ} (h : W.toAffine.Nonsingular a b),
        N • (Affine.Point.some a b h : W.toAffine.Point) = 0 → ‖a‖ ≤ C₀ * N ^ 2

/-- The reference choice of torsion constant from the archimedean existence theorem. -/
noncomputable def torsionConst (c : ℝ)
    (harch : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ LegendreTorsionXBound c C₀) : ℝ :=
  max 1 (Classical.choose harch)

lemma one_le_torsionConst (c : ℝ)
    (harch : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ LegendreTorsionXBound c C₀) :
    1 ≤ torsionConst c harch :=
  le_max_left _ _

lemma torsionConst_spec (c : ℝ)
    (harch : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ LegendreTorsionXBound c C₀) :
    LegendreTorsionXBound c (torsionConst c harch) := by
  intro l hl hl1 W _ hW N hN a b h hP
  have hbound := (Classical.choose_spec harch).2 l hl hl1 W hW hN h hP
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg (N : ℝ)))

end AbcAdaptation.Tripod
